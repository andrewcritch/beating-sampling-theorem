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
import BstLean.Part269Direction25
import BstLean.Part269Shared25
import BstLean.Part269Finite
import BstLean.Part269Rows25
import BstLean.Part269Source
/-! Actual 12988 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12988
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12988 ≤ (1.035406500425 : ℝ) := by
  have hr : (113.964906879267 : ℝ) ≤ √(12988 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.964906879267 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12988 12988 (11 / 1000) ≤
    (0.008387555203 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12988) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.964906879267 : ℝ) ≤ √(12988 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12988)
  have hdiv : K / √(12988 : ℝ) ≤ K / 113.964906879267 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.964906879267 ≤ (0.008387555203 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12988.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12988 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12988 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12988 := gPlus_lower 12988
end BstLean.Part269.N12988

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12988
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035406500424 : ℝ) ≤ wn 12988 := by
  have hn : √(12988 : ℝ) ≤ 113.964906879268 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12988 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.964906879268 ≤ 2 / √(12988 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246199824 : ℝ) ≤ rhoBar 12988 BstLean.Part154.csC ∧
    rhoBar 12988 BstLean.Part154.csC ≤ 0.000246200205 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035406500424 : ℝ) / (1.295212 * 12988) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035406500425 : ℝ) / (1.29521 * 12988) := by gcongr
      _ ≤ (0.000246200205 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12988 BstLean.Part154.csC) ≤ 0.000984861435 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12988 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12988 BstLean.Part154.csC) (piBar (rhoBar 12988 BstLean.Part154.csC)) ≤ 0.000188049180 ∧
    cc1 (rhoBar 12988 BstLean.Part154.csC) (piBar (rhoBar 12988 BstLean.Part154.csC)) ≤ 0.000119656983 ∧
    cc2 (rhoBar 12988 BstLean.Part154.csC) ≤ 0.000069461844 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12988 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12988 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12988 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12988 BstLean.Part154.csC * nuR (rhoBar 12988 BstLean.Part154.csC)) ≤ 0.000492415564 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246200205 : ℝ) * 0.000984861435 := by gcongr
      _ ≤ (0.000492415564 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12988 BstLean.Part154.csC) * nuR (rhoBar 12988 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000984861435 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12988 BstLean.Part154.csC) * rhoBar 12988 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246200205 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246200205 / 2 + 0.399 * 0.000984861435 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188049180 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492415564 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119656983 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246200205 / 1.414213562 := by gcongr
      _ ≤ (0.000069461844 : ℝ) := by norm_num

end BstLean.Part269.N12988

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12988
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12988 BstLean.Part154.csC) (piBar (rhoBar 12988 BstLean.Part154.csC)) ≤ 1.52714E-7 := by
  have hr0 : 0 ≤ rhoBar 12988 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12988 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12988 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12988 BstLean.Part154.csC) (piBar (rhoBar 12988 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12988 BstLean.Part154.csC) (piBar (rhoBar 12988 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12988 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188049180 : ℝ) ^ 2 + 0.000119656983 ^ 2 + 3 * 0.000069461844 ^ 2 +
        2 * 0.797885 * 0.000188049180 * 0.000119656983 + 2 * 0.000188049180 * 0.000069461844 +
        4 * 0.797885 * 0.000119656983 * 0.000069461844 := by gcongr
    _ ≤ (1.52714E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12988 BstLean.Part154.csC Θ ≤ 0.002568987512 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12988 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12988 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12988 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12988 BstLean.Part154.csC) (piBar (rhoBar 12988 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12988 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035406500425 * 1.52714E-7 / (0.000246199824 : ℝ) := by gcongr
    _ ≤ 0.002568987512 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12988 BstLean.Part154.csC Θ ≤ 0.002849317970 + 0.000649141691 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12988 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12988 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12988 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035406500425 : ℝ) * ((2 * Θ * 0.000246200205 +
        (6863 / 10000) * 0.000246200205 * 12988 * 0.000984861435) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002849317970 + 0.000649141691 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12988 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12988 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12988 0.011 Θ ∧ gammaRatio 12988 0.011 Θ ≤ 0.000084637264 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12988 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035406500425 : ℝ) * 0.525 / ((1 - 0.011) * 12988) := by gcongr
      _ ≤ (0.000084637264 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12988 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12988 0.011 Θ) :=
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
    badAllowance 12988 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12988 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12988 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12988 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12988 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12988 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12988 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12988 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12988 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12988 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12988 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035406500425 : ℝ) * 12988 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12988 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003271153193 + 0.003218129203 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12988

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12988
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12988 BstLean.Part154.csC) (piBar (rhoBar 12988 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12988 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12988 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12988 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12988 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12988 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12988 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12988 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12988 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12988 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12988 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12988 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12988 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12988 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12988 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051892874414 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12988) ≤ 0.010478994050 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12988 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035406500425)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010478994050 + 2 * 0.737676 / 12988) := by gcongr
    _ ≤ (0.051892874414 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12988 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12988

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12988
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516303703 : ℝ) ≤ plow 12988 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12988) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052467271025)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348718444) : eMP 12988 0.011 xi bn ≤ 0.001161504914 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12988 : ℝ) * (1 - 0.011))) ≤ 0.000574336376 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001348718444 / (12988 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574336376 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574336376 : ℝ) + 3.141593 * 0.052467271025 / (12988 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001161504914 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052467271025)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348718444) : PiBarMP 12988 12 0.011 xi bn ≤ 0.159435445249 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12988 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036724902233 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.336366626074 : ℝ) ≤ √((12988 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.964906879267 : ℝ) ≤ √(12988 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12988) ≤ 0.122251740859 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036724902233 + 0.052467271025 * 1.772454 / (2 * (113.336366626074 : ℝ))) * (1 + 0.001161504914) +
        8 / (12988 * 113.964906879267) + 0.122251740859 := by gcongr
    _ ≤ (0.159435445249 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052467271025)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348718444) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280950227549) :
    parallelOracle 12988 0.011 xi bn cd ≤ 0.160403886288 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12988 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12988 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516303703 : ℝ) ≤ plow 12988 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.964906879267 : ℝ) ≤ √(12988 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280950227549 : ℝ) / (2 * 0.560516303703 * 113.964906879267)) * 0.159435445249 +
        0.280950227549 ^ 2 / (2 * 0.560516303703 * 113.964906879267) := by gcongr
    _ ≤ (0.160403886288 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052467271025) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348718444)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280950227549) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12988 12988 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516303703 : ℝ) ≤ plow 12988 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.964906879267 : ℝ) ≤ √(12988 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12988 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12988 Θ 1.22 ≤ 0.011636042501 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.964906879267 := by gcongr <;> linarith
      _ ≤ (0.011636042501 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12988 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12988 12988 0.011 ≤ 0.008387555203 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12988 12988 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12988 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12988 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12988 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12988 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160403886288 + 0.011636042501 + (0.008387555203 : ℝ) *
        (1 + 2 * (0.280950227549 + 0.011636042501) / (0.560516303703 * 113.964906879267))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12988]

end BstLean.Part269.N12988

/-! The original eight local profiles supply actual 12988 moment certificates. -/
namespace BstLean.Part269.N12988
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12988 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12988 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12988 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052467271025 ∧
    0 ≤ bN 12988 BstLean.Part154.csC (groupTheta g) ∧ bN 12988 BstLean.Part154.csC (groupTheta g) ≤ 0.001348718444 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12988 12988 0.011
      (momentAllowance 12988 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12988 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12988 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12988 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12988 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12988 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229057353135 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12988 0.011
      (momentAllowance 12988 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12988 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12988
/-! The actual computed-centre upper energy formula at 12988. -/
namespace BstLean.Part269.N12988
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12988

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12988
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12988)
open BstLean.Part268 (cell12988)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084691596581
  | 2 => 0.085620686712
  | 3 => 0.086546049486
  | 4 => 0.087468664129
  | 5 => 0.088389728000
  | 6 => 0.089310690601
  | 7 => 0.090233291095
  | 8 => 0.091159599413
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12988 12988 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12988 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12988

/-! Actual upper energy certificates on all 43 source endpoints at 12988. -/
namespace BstLean.Part269.N12988
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12988)
open BstLean.Part268 (cell12988)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12988 (gMinus 12988) (1 - (cell12988 i).lower) ≤ 1 ∧
    energyUpper 12988 (gMinus 12988) (BstLean.Part211.gPlus 12988)
      (finiteEnergy 12988 12988 0.011) (1 - (cell12988 i).lower) ≤
      (cell12988 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨10,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨11,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨12,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨13,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨14,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨15,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨16,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨17,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨18,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨19,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨20,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨21,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨22,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨23,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨24,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨25,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨26,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨27,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨28,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨29,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨30,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨31,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨32,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨33,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨34,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨35,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨36,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨37,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨38,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨39,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨40,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨41,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨42,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨43,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨44,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨45,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨46,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨47,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨48,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨49,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨50,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨51,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12988) (by norm_num)
        (q := 1 - (cell12988 ⟨52,by decide⟩).lower)
        (by norm_num [cell12988]) (by norm_num [cell12988])
      exact ⟨E.1,E.2.trans (by norm_num [cell12988])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12988

/-! Source-cell containment and simple scalar guards at 12988. -/
namespace BstLean.Part269.N12988
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12988)
open BstLean.Part268 (cell12988)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12988 ⟨10,by decide⟩).lower ∧ (cell12988 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12988 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12988 ⟨11,by decide⟩).lower ∧ (cell12988 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12988 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12988 ⟨12,by decide⟩).lower ∧ (cell12988 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12988 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12988 ⟨13,by decide⟩).lower ∧ (cell12988 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12988 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12988 ⟨14,by decide⟩).lower ∧ (cell12988 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12988 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12988 ⟨15,by decide⟩).lower ∧ (cell12988 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12988 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12988 ⟨16,by decide⟩).lower ∧ (cell12988 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12988 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12988 ⟨17,by decide⟩).lower ∧ (cell12988 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12988 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12988 ⟨18,by decide⟩).lower ∧ (cell12988 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12988 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12988 ⟨19,by decide⟩).lower ∧ (cell12988 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12988 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12988 ⟨20,by decide⟩).lower ∧ (cell12988 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12988 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12988 ⟨21,by decide⟩).lower ∧ (cell12988 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12988 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12988 ⟨22,by decide⟩).lower ∧ (cell12988 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12988 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12988 ⟨23,by decide⟩).lower ∧ (cell12988 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12988 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12988 ⟨24,by decide⟩).lower ∧ (cell12988 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12988 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12988 ⟨25,by decide⟩).lower ∧ (cell12988 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12988 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12988 ⟨26,by decide⟩).lower ∧ (cell12988 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12988 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12988 ⟨27,by decide⟩).lower ∧ (cell12988 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12988 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12988 ⟨28,by decide⟩).lower ∧ (cell12988 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12988 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12988 ⟨29,by decide⟩).lower ∧ (cell12988 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12988 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12988 ⟨30,by decide⟩).lower ∧ (cell12988 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12988 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12988 ⟨31,by decide⟩).lower ∧ (cell12988 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12988 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12988 ⟨32,by decide⟩).lower ∧ (cell12988 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12988 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12988 ⟨33,by decide⟩).lower ∧ (cell12988 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12988 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12988 ⟨34,by decide⟩).lower ∧ (cell12988 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12988 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12988 ⟨35,by decide⟩).lower ∧ (cell12988 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12988 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12988 ⟨36,by decide⟩).lower ∧ (cell12988 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12988 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12988 ⟨37,by decide⟩).lower ∧ (cell12988 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12988 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12988 ⟨38,by decide⟩).lower ∧ (cell12988 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12988 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12988 ⟨39,by decide⟩).lower ∧ (cell12988 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12988 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12988 ⟨40,by decide⟩).lower ∧ (cell12988 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12988 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12988 ⟨41,by decide⟩).lower ∧ (cell12988 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12988 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12988 ⟨42,by decide⟩).lower ∧ (cell12988 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12988 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12988 ⟨43,by decide⟩).lower ∧ (cell12988 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12988 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12988 ⟨44,by decide⟩).lower ∧ (cell12988 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12988 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12988 ⟨45,by decide⟩).lower ∧ (cell12988 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12988 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12988 ⟨46,by decide⟩).lower ∧ (cell12988 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12988 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12988 ⟨47,by decide⟩).lower ∧ (cell12988 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12988 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12988 ⟨48,by decide⟩).lower ∧ (cell12988 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12988 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12988 ⟨49,by decide⟩).lower ∧ (cell12988 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12988 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12988 ⟨50,by decide⟩).lower ∧ (cell12988 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12988 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12988 ⟨51,by decide⟩).lower ∧ (cell12988 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12988 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12988 ⟨52,by decide⟩).lower ∧ (cell12988 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12988 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12988 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12988 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12988,cell12988,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12988 i).lower ∧
    (cell12988 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12988 i).upper ≤ (0.532 : ℝ) ∧
    (cell12988 i).centre ≤ (0.1 : ℝ) ∧ (cell12988 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12988 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12988 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12988

/-! The local source numeric instances at 12988 have no network premises. -/
namespace BstLean.Part269.N12988
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12988)
open BstLean.Part268 (cell12988)

noncomputable def sourceNumerics12988 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12988 (cell12988 i)
      scalarRow12988.M scalarRow12988.H scalarRow12988.xi := by
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
    energy_allowance := scalarRow12988.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12988]
    centre_nonneg := (scalarRow12988.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12988])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12988
/-! Actual 12989 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12989
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12989 ≤ (1.035405125602 : ℝ) := by
  have hr : (113.969294110299 : ℝ) ≤ √(12989 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.969294110299 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12989 12989 (11 / 1000) ≤
    (0.008387232323 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12989) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.969294110299 : ℝ) ≤ √(12989 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12989)
  have hdiv : K / √(12989 : ℝ) ≤ K / 113.969294110299 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.969294110299 ≤ (0.008387232323 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12989.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12989 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12989 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12989 := gPlus_lower 12989
end BstLean.Part269.N12989

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12989
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035405125601 : ℝ) ≤ wn 12989 := by
  have hn : √(12989 : ℝ) ≤ 113.969294110300 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12989 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.969294110300 ≤ 2 / √(12989 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246180543 : ℝ) ≤ rhoBar 12989 BstLean.Part154.csC ∧
    rhoBar 12989 BstLean.Part154.csC ≤ 0.000246180924 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035405125601 : ℝ) / (1.295212 * 12989) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035405125602 : ℝ) / (1.29521 * 12989) := by gcongr
      _ ≤ (0.000246180924 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12989 BstLean.Part154.csC) ≤ 0.000984784302 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12989 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12989 BstLean.Part154.csC) (piBar (rhoBar 12989 BstLean.Part154.csC)) ≤ 0.000188034453 ∧
    cc1 (rhoBar 12989 BstLean.Part154.csC) (piBar (rhoBar 12989 BstLean.Part154.csC)) ≤ 0.000119647612 ∧
    cc2 (rhoBar 12989 BstLean.Part154.csC) ≤ 0.000069456405 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12989 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12989 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12989 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12989 BstLean.Part154.csC * nuR (rhoBar 12989 BstLean.Part154.csC)) ≤ 0.000492377000 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246180924 : ℝ) * 0.000984784302 := by gcongr
      _ ≤ (0.000492377000 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12989 BstLean.Part154.csC) * nuR (rhoBar 12989 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000984784302 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12989 BstLean.Part154.csC) * rhoBar 12989 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246180924 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246180924 / 2 + 0.399 * 0.000984784302 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188034453 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492377000 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119647612 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246180924 / 1.414213562 := by gcongr
      _ ≤ (0.000069456405 : ℝ) := by norm_num

end BstLean.Part269.N12989

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12989
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12989 BstLean.Part154.csC) (piBar (rhoBar 12989 BstLean.Part154.csC)) ≤ 1.52690E-7 := by
  have hr0 : 0 ≤ rhoBar 12989 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12989 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12989 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12989 BstLean.Part154.csC) (piBar (rhoBar 12989 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12989 BstLean.Part154.csC) (piBar (rhoBar 12989 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12989 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188034453 : ℝ) ^ 2 + 0.000119647612 ^ 2 + 3 * 0.000069456405 ^ 2 +
        2 * 0.797885 * 0.000188034453 * 0.000119647612 + 2 * 0.000188034453 * 0.000069456405 +
        4 * 0.797885 * 0.000119647612 * 0.000069456405 := by gcongr
    _ ≤ (1.52690E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12989 BstLean.Part154.csC Θ ≤ 0.002568781541 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12989 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12989 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12989 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12989 BstLean.Part154.csC) (piBar (rhoBar 12989 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12989 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035405125602 * 1.52690E-7 / (0.000246180543 : ℝ) := by gcongr
    _ ≤ 0.002568781541 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12989 BstLean.Part154.csC Θ ≤ 0.002849087254 + 0.000649089992 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12989 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12989 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12989 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035405125602 : ℝ) * ((2 * Θ * 0.000246180924 +
        (6863 / 10000) * 0.000246180924 * 12989 * 0.000984784302) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002849087254 + 0.000649089992 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12989 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12989 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12989 0.011 Θ ∧ gammaRatio 12989 0.011 Θ ≤ 0.000084630636 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12989 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035405125602 : ℝ) * 0.525 / ((1 - 0.011) * 12989) := by gcongr
      _ ≤ (0.000084630636 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12989 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12989 0.011 Θ) :=
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
    badAllowance 12989 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12989 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12989 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12989 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12989 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12989 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12989 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12989 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12989 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12989 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12989 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035405125602 : ℝ) * 12989 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12989 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003270922477 + 0.003217871533 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12989

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12989
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12989 BstLean.Part154.csC) (piBar (rhoBar 12989 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12989 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12989 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12989 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12989 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12989 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12989 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12989 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12989 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12989 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12989 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12989 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12989 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12989 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12989 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051890855385 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12989) ≤ 0.010478590663 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12989 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035405125602)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010478590663 + 2 * 0.737676 / 12989) := by gcongr
    _ ≤ (0.051890855385 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12989 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12989

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12989
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516346939 : ℝ) ≤ plow 12989 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12989) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052466905032)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348610310) : eMP 12989 0.011 xi bn ≤ 0.001161413571 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12989 : ℝ) * (1 - 0.011))) ≤ 0.000574291243 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001348610310 / (12989 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574291243 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574291243 : ℝ) + 3.141593 * 0.052466905032 / (12989 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001161413571 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052466905032)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348610310) : PiBarMP 12989 12 0.011 xi bn ≤ 0.159429242537 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12989 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036723429987 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.340729660612 : ℝ) ≤ √((12989 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.969294110299 : ℝ) ≤ √(12989 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12989) ≤ 0.122247034796 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036723429987 + 0.052466905032 * 1.772454 / (2 * (113.340729660612 : ℝ))) * (1 + 0.001161413571) +
        8 / (12989 * 113.969294110299) + 0.122247034796 := by gcongr
    _ ≤ (0.159429242537 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052466905032)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348610310) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280947409607) :
    parallelOracle 12989 0.011 xi bn cd ≤ 0.160397616672 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12989 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12989 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516346939 : ℝ) ≤ plow 12989 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.969294110299 : ℝ) ≤ √(12989 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280947409607 : ℝ) / (2 * 0.560516346939 * 113.969294110299)) * 0.159429242537 +
        0.280947409607 ^ 2 / (2 * 0.560516346939 * 113.969294110299) := by gcongr
    _ ≤ (0.160397616672 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052466905032) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348610310)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280947409607) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12989 12989 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516346939 : ℝ) ≤ plow 12989 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.969294110299 : ℝ) ≤ √(12989 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12989 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12989 Θ 1.22 ≤ 0.011635594573 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.969294110299 := by gcongr <;> linarith
      _ ≤ (0.011635594573 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12989 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12989 12989 0.011 ≤ 0.008387232323 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12989 12989 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12989 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12989 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12989 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12989 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160397616672 + 0.011635594573 + (0.008387232323 : ℝ) *
        (1 + 2 * (0.280947409607 + 0.011635594573) / (0.560516346939 * 113.969294110299))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12989]

end BstLean.Part269.N12989

/-! The original eight local profiles supply actual 12989 moment certificates. -/
namespace BstLean.Part269.N12989
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12989 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12989 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12989 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052466905032 ∧
    0 ≤ bN 12989 BstLean.Part154.csC (groupTheta g) ∧ bN 12989 BstLean.Part154.csC (groupTheta g) ≤ 0.001348610310 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12989 12989 0.011
      (momentAllowance 12989 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12989 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12989 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12989 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12989 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12989 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229056554222 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12989 0.011
      (momentAllowance 12989 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12989 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12989
/-! The actual computed-centre upper energy formula at 12989. -/
namespace BstLean.Part269.N12989
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12989

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12989
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12989)
open BstLean.Part268 (cell12989)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084688968630
  | 2 => 0.085618023868
  | 3 => 0.086543346411
  | 4 => 0.087465914235
  | 5 => 0.088386923225
  | 6 => 0.089307821153
  | 7 => 0.090230345159
  | 8 => 0.091156562835
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12989 12989 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12989 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12989

/-! Actual upper energy certificates on all 43 source endpoints at 12989. -/
namespace BstLean.Part269.N12989
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12989)
open BstLean.Part268 (cell12989)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12989 (gMinus 12989) (1 - (cell12989 i).lower) ≤ 1 ∧
    energyUpper 12989 (gMinus 12989) (BstLean.Part211.gPlus 12989)
      (finiteEnergy 12989 12989 0.011) (1 - (cell12989 i).lower) ≤
      (cell12989 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨10,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨11,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨12,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨13,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨14,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨15,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨16,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨17,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨18,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨19,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨20,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨21,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨22,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨23,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨24,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨25,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨26,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨27,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨28,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨29,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨30,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨31,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨32,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨33,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨34,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨35,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨36,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨37,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨38,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨39,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨40,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨41,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨42,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨43,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨44,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨45,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨46,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨47,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨48,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨49,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨50,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨51,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12989) (by norm_num)
        (q := 1 - (cell12989 ⟨52,by decide⟩).lower)
        (by norm_num [cell12989]) (by norm_num [cell12989])
      exact ⟨E.1,E.2.trans (by norm_num [cell12989])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12989

/-! Source-cell containment and simple scalar guards at 12989. -/
namespace BstLean.Part269.N12989
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12989)
open BstLean.Part268 (cell12989)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12989 ⟨10,by decide⟩).lower ∧ (cell12989 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12989 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12989 ⟨11,by decide⟩).lower ∧ (cell12989 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12989 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12989 ⟨12,by decide⟩).lower ∧ (cell12989 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12989 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12989 ⟨13,by decide⟩).lower ∧ (cell12989 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12989 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12989 ⟨14,by decide⟩).lower ∧ (cell12989 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12989 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12989 ⟨15,by decide⟩).lower ∧ (cell12989 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12989 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12989 ⟨16,by decide⟩).lower ∧ (cell12989 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12989 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12989 ⟨17,by decide⟩).lower ∧ (cell12989 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12989 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12989 ⟨18,by decide⟩).lower ∧ (cell12989 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12989 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12989 ⟨19,by decide⟩).lower ∧ (cell12989 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12989 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12989 ⟨20,by decide⟩).lower ∧ (cell12989 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12989 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12989 ⟨21,by decide⟩).lower ∧ (cell12989 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12989 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12989 ⟨22,by decide⟩).lower ∧ (cell12989 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12989 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12989 ⟨23,by decide⟩).lower ∧ (cell12989 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12989 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12989 ⟨24,by decide⟩).lower ∧ (cell12989 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12989 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12989 ⟨25,by decide⟩).lower ∧ (cell12989 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12989 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12989 ⟨26,by decide⟩).lower ∧ (cell12989 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12989 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12989 ⟨27,by decide⟩).lower ∧ (cell12989 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12989 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12989 ⟨28,by decide⟩).lower ∧ (cell12989 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12989 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12989 ⟨29,by decide⟩).lower ∧ (cell12989 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12989 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12989 ⟨30,by decide⟩).lower ∧ (cell12989 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12989 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12989 ⟨31,by decide⟩).lower ∧ (cell12989 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12989 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12989 ⟨32,by decide⟩).lower ∧ (cell12989 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12989 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12989 ⟨33,by decide⟩).lower ∧ (cell12989 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12989 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12989 ⟨34,by decide⟩).lower ∧ (cell12989 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12989 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12989 ⟨35,by decide⟩).lower ∧ (cell12989 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12989 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12989 ⟨36,by decide⟩).lower ∧ (cell12989 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12989 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12989 ⟨37,by decide⟩).lower ∧ (cell12989 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12989 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12989 ⟨38,by decide⟩).lower ∧ (cell12989 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12989 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12989 ⟨39,by decide⟩).lower ∧ (cell12989 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12989 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12989 ⟨40,by decide⟩).lower ∧ (cell12989 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12989 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12989 ⟨41,by decide⟩).lower ∧ (cell12989 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12989 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12989 ⟨42,by decide⟩).lower ∧ (cell12989 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12989 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12989 ⟨43,by decide⟩).lower ∧ (cell12989 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12989 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12989 ⟨44,by decide⟩).lower ∧ (cell12989 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12989 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12989 ⟨45,by decide⟩).lower ∧ (cell12989 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12989 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12989 ⟨46,by decide⟩).lower ∧ (cell12989 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12989 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12989 ⟨47,by decide⟩).lower ∧ (cell12989 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12989 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12989 ⟨48,by decide⟩).lower ∧ (cell12989 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12989 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12989 ⟨49,by decide⟩).lower ∧ (cell12989 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12989 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12989 ⟨50,by decide⟩).lower ∧ (cell12989 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12989 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12989 ⟨51,by decide⟩).lower ∧ (cell12989 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12989 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12989 ⟨52,by decide⟩).lower ∧ (cell12989 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12989 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12989 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12989 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12989,cell12989,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12989 i).lower ∧
    (cell12989 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12989 i).upper ≤ (0.532 : ℝ) ∧
    (cell12989 i).centre ≤ (0.1 : ℝ) ∧ (cell12989 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12989 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12989 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12989

/-! The local source numeric instances at 12989 have no network premises. -/
namespace BstLean.Part269.N12989
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12989)
open BstLean.Part268 (cell12989)

noncomputable def sourceNumerics12989 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12989 (cell12989 i)
      scalarRow12989.M scalarRow12989.H scalarRow12989.xi := by
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
    energy_allowance := scalarRow12989.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12989]
    centre_nonneg := (scalarRow12989.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12989])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12989
/-! Actual 12990 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12990
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12990 ≤ (1.035403750939 : ℝ) := by
  have hr : (113.973681172453 : ℝ) ≤ √(12990 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.973681172453 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12990 12990 (11 / 1000) ≤
    (0.008386909480 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12990) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.973681172453 : ℝ) ≤ √(12990 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12990)
  have hdiv : K / √(12990 : ℝ) ≤ K / 113.973681172453 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.973681172453 ≤ (0.008386909480 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12990.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12990 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12990 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12990 := gPlus_lower 12990
end BstLean.Part269.N12990

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12990
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035403750938 : ℝ) ≤ wn 12990 := by
  have hn : √(12990 : ℝ) ≤ 113.973681172454 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12990 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.973681172454 ≤ 2 / √(12990 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246161264 : ℝ) ≤ rhoBar 12990 BstLean.Part154.csC ∧
    rhoBar 12990 BstLean.Part154.csC ≤ 0.000246161645 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035403750938 : ℝ) / (1.295212 * 12990) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035403750939 : ℝ) / (1.29521 * 12990) := by gcongr
      _ ≤ (0.000246161645 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12990 BstLean.Part154.csC) ≤ 0.000984707176 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12990 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12990 BstLean.Part154.csC) (piBar (rhoBar 12990 BstLean.Part154.csC)) ≤ 0.000188019726 ∧
    cc1 (rhoBar 12990 BstLean.Part154.csC) (piBar (rhoBar 12990 BstLean.Part154.csC)) ≤ 0.000119638241 ∧
    cc2 (rhoBar 12990 BstLean.Part154.csC) ≤ 0.000069450965 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12990 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12990 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12990 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12990 BstLean.Part154.csC * nuR (rhoBar 12990 BstLean.Part154.csC)) ≤ 0.000492338439 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246161645 : ℝ) * 0.000984707176 := by gcongr
      _ ≤ (0.000492338439 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12990 BstLean.Part154.csC) * nuR (rhoBar 12990 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000984707176 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12990 BstLean.Part154.csC) * rhoBar 12990 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246161645 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246161645 / 2 + 0.399 * 0.000984707176 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188019726 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492338439 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119638241 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246161645 / 1.414213562 := by gcongr
      _ ≤ (0.000069450965 : ℝ) := by norm_num

end BstLean.Part269.N12990

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12990
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12990 BstLean.Part154.csC) (piBar (rhoBar 12990 BstLean.Part154.csC)) ≤ 1.52666E-7 := by
  have hr0 : 0 ≤ rhoBar 12990 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12990 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12990 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12990 BstLean.Part154.csC) (piBar (rhoBar 12990 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12990 BstLean.Part154.csC) (piBar (rhoBar 12990 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12990 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188019726 : ℝ) ^ 2 + 0.000119638241 ^ 2 + 3 * 0.000069450965 ^ 2 +
        2 * 0.797885 * 0.000188019726 * 0.000119638241 + 2 * 0.000188019726 * 0.000069450965 +
        4 * 0.797885 * 0.000119638241 * 0.000069450965 := by gcongr
    _ ≤ (1.52666E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12990 BstLean.Part154.csC Θ ≤ 0.002568575518 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12990 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12990 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12990 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12990 BstLean.Part154.csC) (piBar (rhoBar 12990 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12990 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035403750939 * 1.52666E-7 / (0.000246161264 : ℝ) := by gcongr
    _ ≤ 0.002568575518 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12990 BstLean.Part154.csC Θ ≤ 0.002848856548 + 0.000649038298 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12990 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12990 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12990 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035403750939 : ℝ) * ((2 * Θ * 0.000246161645 +
        (6863 / 10000) * 0.000246161645 * 12990 * 0.000984707176) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002848856548 + 0.000649038298 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12990 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12990 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12990 0.011 Θ ∧ gammaRatio 12990 0.011 Θ ≤ 0.000084624008 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12990 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035403750939 : ℝ) * 0.525 / ((1 - 0.011) * 12990) := by gcongr
      _ ≤ (0.000084624008 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12990 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12990 0.011 Θ) :=
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
    badAllowance 12990 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12990 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12990 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12990 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12990 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12990 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 12990 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12990 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12990 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12990 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12990 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035403750939 : ℝ) * 12990 *
        (1.5230E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12990 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003270691771 + 0.003217613816 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12990

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12990
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12990 BstLean.Part154.csC) (piBar (rhoBar 12990 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12990 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12990 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12990 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12990 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12990 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12990 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12990 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12990 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12990 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12990 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12990 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12990 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12990 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12990 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051888836589 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12990) ≤ 0.010478187322 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12990 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035403750939)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010478187322 + 2 * 0.737676 / 12990) := by gcongr
    _ ≤ (0.051888836589 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12990 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12990

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12990
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516390169 : ℝ) ≤ plow 12990 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12990) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052466539025)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348502147) : eMP 12990 0.011 xi bn ≤ 0.001161322224 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12990 : ℝ) * (1 - 0.011))) ≤ 0.000574246108 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001348502147 / (12990 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574246108 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574246108 : ℝ) + 3.141593 * 0.052466539025 / (12990 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001161322224 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052466539025)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348502147) : PiBarMP 12990 12 0.011 xi bn ≤ 0.159423039918 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12990 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036721957288 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.345092527202 : ℝ) ≤ √((12990 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.973681172453 : ℝ) ≤ √(12990 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12990) ≤ 0.122242329277 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036721957288 + 0.052466539025 * 1.772454 / (2 * (113.345092527202 : ℝ))) * (1 + 0.001161322224) +
        8 / (12990 * 113.973681172453) + 0.122242329277 := by gcongr
    _ ≤ (0.159423039918 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052466539025)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348502147) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280944591865) :
    parallelOracle 12990 0.011 xi bn cd ≤ 0.160391347157 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12990 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12990 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516390169 : ℝ) ≤ plow 12990 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.973681172453 : ℝ) ≤ √(12990 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280944591865 : ℝ) / (2 * 0.560516390169 * 113.973681172453)) * 0.159423039918 +
        0.280944591865 ^ 2 / (2 * 0.560516390169 * 113.973681172453) := by gcongr
    _ ≤ (0.160391347157 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052466539025) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348502147)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280944591865) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12990 12990 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516390169 : ℝ) ≤ plow 12990 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.973681172453 : ℝ) ≤ √(12990 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12990 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12990 Θ 1.22 ≤ 0.011635146697 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.973681172453 := by gcongr <;> linarith
      _ ≤ (0.011635146697 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12990 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12990 12990 0.011 ≤ 0.008386909480 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12990 12990 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12990 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12990 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12990 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12990 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160391347157 + 0.011635146697 + (0.008386909480 : ℝ) *
        (1 + 2 * (0.280944591865 + 0.011635146697) / (0.560516390169 * 113.973681172453))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12990]

end BstLean.Part269.N12990

/-! The original eight local profiles supply actual 12990 moment certificates. -/
namespace BstLean.Part269.N12990
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12990 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12990 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12990 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052466539025 ∧
    0 ≤ bN 12990 BstLean.Part154.csC (groupTheta g) ∧ bN 12990 BstLean.Part154.csC (groupTheta g) ≤ 0.001348502147 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12990 12990 0.011
      (momentAllowance 12990 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12990 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12990 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12990 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12990 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12990 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229055755276 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12990 0.011
      (momentAllowance 12990 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12990 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12990
/-! The actual computed-centre upper energy formula at 12990. -/
namespace BstLean.Part269.N12990
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12990

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12990
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12990)
open BstLean.Part268 (cell12990)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084686341495
  | 2 => 0.085615361869
  | 3 => 0.086540644216
  | 4 => 0.087463165266
  | 5 => 0.088384119430
  | 6 => 0.089304952750
  | 7 => 0.090227400350
  | 8 => 0.091153527480
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12990 12990 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12990 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12990

/-! Actual upper energy certificates on all 43 source endpoints at 12990. -/
namespace BstLean.Part269.N12990
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12990)
open BstLean.Part268 (cell12990)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12990 (gMinus 12990) (1 - (cell12990 i).lower) ≤ 1 ∧
    energyUpper 12990 (gMinus 12990) (BstLean.Part211.gPlus 12990)
      (finiteEnergy 12990 12990 0.011) (1 - (cell12990 i).lower) ≤
      (cell12990 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨10,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨11,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨12,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨13,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨14,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨15,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨16,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨17,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨18,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨19,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨20,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨21,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨22,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨23,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨24,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨25,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨26,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨27,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨28,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨29,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨30,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨31,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨32,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨33,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨34,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨35,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨36,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨37,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨38,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨39,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨40,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨41,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨42,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨43,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨44,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨45,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨46,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨47,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨48,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨49,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨50,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨51,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12990) (by norm_num)
        (q := 1 - (cell12990 ⟨52,by decide⟩).lower)
        (by norm_num [cell12990]) (by norm_num [cell12990])
      exact ⟨E.1,E.2.trans (by norm_num [cell12990])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12990

/-! Source-cell containment and simple scalar guards at 12990. -/
namespace BstLean.Part269.N12990
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12990)
open BstLean.Part268 (cell12990)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12990 ⟨10,by decide⟩).lower ∧ (cell12990 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12990 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12990 ⟨11,by decide⟩).lower ∧ (cell12990 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12990 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12990 ⟨12,by decide⟩).lower ∧ (cell12990 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12990 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12990 ⟨13,by decide⟩).lower ∧ (cell12990 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12990 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12990 ⟨14,by decide⟩).lower ∧ (cell12990 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12990 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12990 ⟨15,by decide⟩).lower ∧ (cell12990 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12990 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12990 ⟨16,by decide⟩).lower ∧ (cell12990 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12990 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12990 ⟨17,by decide⟩).lower ∧ (cell12990 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12990 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12990 ⟨18,by decide⟩).lower ∧ (cell12990 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12990 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12990 ⟨19,by decide⟩).lower ∧ (cell12990 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12990 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12990 ⟨20,by decide⟩).lower ∧ (cell12990 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12990 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12990 ⟨21,by decide⟩).lower ∧ (cell12990 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12990 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12990 ⟨22,by decide⟩).lower ∧ (cell12990 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12990 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12990 ⟨23,by decide⟩).lower ∧ (cell12990 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12990 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12990 ⟨24,by decide⟩).lower ∧ (cell12990 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12990 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12990 ⟨25,by decide⟩).lower ∧ (cell12990 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12990 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12990 ⟨26,by decide⟩).lower ∧ (cell12990 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12990 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12990 ⟨27,by decide⟩).lower ∧ (cell12990 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12990 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12990 ⟨28,by decide⟩).lower ∧ (cell12990 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12990 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12990 ⟨29,by decide⟩).lower ∧ (cell12990 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12990 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12990 ⟨30,by decide⟩).lower ∧ (cell12990 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12990 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12990 ⟨31,by decide⟩).lower ∧ (cell12990 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12990 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12990 ⟨32,by decide⟩).lower ∧ (cell12990 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12990 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12990 ⟨33,by decide⟩).lower ∧ (cell12990 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12990 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12990 ⟨34,by decide⟩).lower ∧ (cell12990 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12990 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12990 ⟨35,by decide⟩).lower ∧ (cell12990 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12990 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12990 ⟨36,by decide⟩).lower ∧ (cell12990 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12990 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12990 ⟨37,by decide⟩).lower ∧ (cell12990 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12990 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12990 ⟨38,by decide⟩).lower ∧ (cell12990 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12990 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12990 ⟨39,by decide⟩).lower ∧ (cell12990 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12990 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12990 ⟨40,by decide⟩).lower ∧ (cell12990 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12990 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12990 ⟨41,by decide⟩).lower ∧ (cell12990 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12990 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12990 ⟨42,by decide⟩).lower ∧ (cell12990 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12990 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12990 ⟨43,by decide⟩).lower ∧ (cell12990 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12990 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12990 ⟨44,by decide⟩).lower ∧ (cell12990 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12990 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12990 ⟨45,by decide⟩).lower ∧ (cell12990 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12990 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12990 ⟨46,by decide⟩).lower ∧ (cell12990 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12990 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12990 ⟨47,by decide⟩).lower ∧ (cell12990 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12990 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12990 ⟨48,by decide⟩).lower ∧ (cell12990 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12990 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12990 ⟨49,by decide⟩).lower ∧ (cell12990 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12990 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12990 ⟨50,by decide⟩).lower ∧ (cell12990 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12990 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12990 ⟨51,by decide⟩).lower ∧ (cell12990 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12990 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12990 ⟨52,by decide⟩).lower ∧ (cell12990 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12990 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12990 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12990 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12990,cell12990,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12990 i).lower ∧
    (cell12990 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12990 i).upper ≤ (0.532 : ℝ) ∧
    (cell12990 i).centre ≤ (0.1 : ℝ) ∧ (cell12990 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12990 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12990 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12990

/-! The local source numeric instances at 12990 have no network premises. -/
namespace BstLean.Part269.N12990
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12990)
open BstLean.Part268 (cell12990)

noncomputable def sourceNumerics12990 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12990 (cell12990 i)
      scalarRow12990.M scalarRow12990.H scalarRow12990.xi := by
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
    energy_allowance := scalarRow12990.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12990]
    centre_nonneg := (scalarRow12990.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12990])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12990
/-! Actual 12991 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12991
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12991 ≤ (1.035402376435 : ℝ) := by
  have hr : (113.978068065746 : ℝ) ≤ √(12991 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.978068065746 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12991 12991 (11 / 1000) ≤
    (0.008386586674 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12991) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.978068065746 : ℝ) ≤ √(12991 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12991)
  have hdiv : K / √(12991 : ℝ) ≤ K / 113.978068065746 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.978068065746 ≤ (0.008386586674 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12991.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12991 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12991 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12991 := gPlus_lower 12991
end BstLean.Part269.N12991

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12991
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035402376434 : ℝ) ≤ wn 12991 := by
  have hn : √(12991 : ℝ) ≤ 113.978068065747 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12991 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.978068065747 ≤ 2 / √(12991 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246141989 : ℝ) ≤ rhoBar 12991 BstLean.Part154.csC ∧
    rhoBar 12991 BstLean.Part154.csC ≤ 0.000246142370 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035402376434 : ℝ) / (1.295212 * 12991) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035402376435 : ℝ) / (1.29521 * 12991) := by gcongr
      _ ≤ (0.000246142370 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12991 BstLean.Part154.csC) ≤ 0.000984630067 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12991 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12991 BstLean.Part154.csC) (piBar (rhoBar 12991 BstLean.Part154.csC)) ≤ 0.000188005004 ∧
    cc1 (rhoBar 12991 BstLean.Part154.csC) (piBar (rhoBar 12991 BstLean.Part154.csC)) ≤ 0.000119628873 ∧
    cc2 (rhoBar 12991 BstLean.Part154.csC) ≤ 0.000069445527 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12991 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12991 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12991 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12991 BstLean.Part154.csC * nuR (rhoBar 12991 BstLean.Part154.csC)) ≤ 0.000492299887 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246142370 : ℝ) * 0.000984630067 := by gcongr
      _ ≤ (0.000492299887 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12991 BstLean.Part154.csC) * nuR (rhoBar 12991 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000984630067 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12991 BstLean.Part154.csC) * rhoBar 12991 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246142370 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246142370 / 2 + 0.399 * 0.000984630067 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188005004 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492299887 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119628873 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246142370 / 1.414213562 := by gcongr
      _ ≤ (0.000069445527 : ℝ) := by norm_num

end BstLean.Part269.N12991

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12991
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12991 BstLean.Part154.csC) (piBar (rhoBar 12991 BstLean.Part154.csC)) ≤ 1.52642E-7 := by
  have hr0 : 0 ≤ rhoBar 12991 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12991 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12991 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12991 BstLean.Part154.csC) (piBar (rhoBar 12991 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12991 BstLean.Part154.csC) (piBar (rhoBar 12991 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12991 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188005004 : ℝ) ^ 2 + 0.000119628873 ^ 2 + 3 * 0.000069445527 ^ 2 +
        2 * 0.797885 * 0.000188005004 * 0.000119628873 + 2 * 0.000188005004 * 0.000069445527 +
        4 * 0.797885 * 0.000119628873 * 0.000069445527 := by gcongr
    _ ≤ (1.52642E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12991 BstLean.Part154.csC Θ ≤ 0.002568369423 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12991 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12991 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12991 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12991 BstLean.Part154.csC) (piBar (rhoBar 12991 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12991 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035402376435 * 1.52642E-7 / (0.000246141989 : ℝ) := by gcongr
    _ ≤ 0.002568369423 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12991 BstLean.Part154.csC Θ ≤ 0.002848625906 + 0.000648986616 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12991 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12991 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12991 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035402376435 : ℝ) * ((2 * Θ * 0.000246142370 +
        (6863 / 10000) * 0.000246142370 * 12991 * 0.000984630067) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002848625906 + 0.000648986616 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12991 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12991 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12991 0.011 Θ ∧ gammaRatio 12991 0.011 Θ ≤ 0.000084617382 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12991 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035402376435 : ℝ) * 0.525 / ((1 - 0.011) * 12991) := by gcongr
      _ ≤ (0.000084617382 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12991 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12991 0.011 Θ) :=
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
    badAllowance 12991 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12991 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12991 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12991 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12991 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12991 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 12991 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12991 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12991 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12991 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12991 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035402376435 : ℝ) * 12991 *
        (1.5230E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12991 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003270461129 + 0.003217356039 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12991

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12991
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12991 BstLean.Part154.csC) (piBar (rhoBar 12991 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12991 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12991 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12991 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12991 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12991 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12991 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12991 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12991 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12991 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12991 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12991 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12991 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12991 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12991 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051886818030 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12991) ≤ 0.010477784028 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12991 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035402376435)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010477784028 + 2 * 0.737676 / 12991) := by gcongr
    _ ≤ (0.051886818030 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12991 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12991

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12991
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516433392 : ℝ) ≤ plow 12991 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12991) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052466173050)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348393948) : eMP 12991 0.011 xi bn ≤ 0.001161230868 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12991 : ℝ) * (1 - 0.011))) ≤ 0.000574200969 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001348393948 / (12991 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574200969 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574200969 : ℝ) + 3.141593 * 0.052466173050 / (12991 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001161230868 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052466173050)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348393948) : PiBarMP 12991 12 0.011 xi bn ≤ 0.159416837294 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12991 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036720484039 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.349455225863 : ℝ) ≤ √((12991 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.978068065746 : ℝ) ≤ √(12991 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12991) ≤ 0.122237624301 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036720484039 + 0.052466173050 * 1.772454 / (2 * (113.349455225863 : ℝ))) * (1 + 0.001161230868) +
        8 / (12991 * 113.978068065746) + 0.122237624301 := by gcongr
    _ ≤ (0.159416837294 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052466173050)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348393948) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280941774427) :
    parallelOracle 12991 0.011 xi bn cd ≤ 0.160385077646 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12991 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12991 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516433392 : ℝ) ≤ plow 12991 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.978068065746 : ℝ) ≤ √(12991 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280941774427 : ℝ) / (2 * 0.560516433392 * 113.978068065746)) * 0.159416837294 +
        0.280941774427 ^ 2 / (2 * 0.560516433392 * 113.978068065746) := by gcongr
    _ ≤ (0.160385077646 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052466173050) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348393948)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280941774427) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12991 12991 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516433392 : ℝ) ≤ plow 12991 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.978068065746 : ℝ) ≤ √(12991 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12991 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12991 Θ 1.22 ≤ 0.011634698873 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.978068065746 := by gcongr <;> linarith
      _ ≤ (0.011634698873 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12991 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12991 12991 0.011 ≤ 0.008386586674 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12991 12991 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12991 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12991 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12991 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12991 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160385077646 + 0.011634698873 + (0.008386586674 : ℝ) *
        (1 + 2 * (0.280941774427 + 0.011634698873) / (0.560516433392 * 113.978068065746))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12991]

end BstLean.Part269.N12991

/-! The original eight local profiles supply actual 12991 moment certificates. -/
namespace BstLean.Part269.N12991
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12991 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12991 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12991 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052466173050 ∧
    0 ≤ bN 12991 BstLean.Part154.csC (groupTheta g) ∧ bN 12991 BstLean.Part154.csC (groupTheta g) ≤ 0.001348393948 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12991 12991 0.011
      (momentAllowance 12991 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12991 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12991 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12991 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12991 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12991 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229054956397 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12991 0.011
      (momentAllowance 12991 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12991 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12991
/-! The actual computed-centre upper energy formula at 12991. -/
namespace BstLean.Part269.N12991
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12991

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12991
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12991)
open BstLean.Part268 (cell12991)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084683715174
  | 2 => 0.085612700714
  | 3 => 0.086537942901
  | 4 => 0.087460417220
  | 5 => 0.088381316613
  | 6 => 0.089302085392
  | 7 => 0.090224456666
  | 8 => 0.091150493348
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12991 12991 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12991 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12991

/-! Actual upper energy certificates on all 43 source endpoints at 12991. -/
namespace BstLean.Part269.N12991
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12991)
open BstLean.Part268 (cell12991)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12991 (gMinus 12991) (1 - (cell12991 i).lower) ≤ 1 ∧
    energyUpper 12991 (gMinus 12991) (BstLean.Part211.gPlus 12991)
      (finiteEnergy 12991 12991 0.011) (1 - (cell12991 i).lower) ≤
      (cell12991 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨10,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨11,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨12,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨13,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨14,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨15,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨16,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨17,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨18,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨19,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨20,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨21,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨22,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨23,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨24,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨25,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨26,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨27,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨28,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨29,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨30,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨31,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨32,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨33,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨34,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨35,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨36,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨37,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨38,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨39,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨40,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨41,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨42,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨43,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨44,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨45,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨46,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨47,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨48,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨49,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨50,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨51,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12991) (by norm_num)
        (q := 1 - (cell12991 ⟨52,by decide⟩).lower)
        (by norm_num [cell12991]) (by norm_num [cell12991])
      exact ⟨E.1,E.2.trans (by norm_num [cell12991])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12991

/-! Source-cell containment and simple scalar guards at 12991. -/
namespace BstLean.Part269.N12991
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12991)
open BstLean.Part268 (cell12991)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12991 ⟨10,by decide⟩).lower ∧ (cell12991 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12991 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12991 ⟨11,by decide⟩).lower ∧ (cell12991 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12991 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12991 ⟨12,by decide⟩).lower ∧ (cell12991 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12991 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12991 ⟨13,by decide⟩).lower ∧ (cell12991 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12991 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12991 ⟨14,by decide⟩).lower ∧ (cell12991 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12991 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12991 ⟨15,by decide⟩).lower ∧ (cell12991 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12991 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12991 ⟨16,by decide⟩).lower ∧ (cell12991 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12991 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12991 ⟨17,by decide⟩).lower ∧ (cell12991 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12991 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12991 ⟨18,by decide⟩).lower ∧ (cell12991 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12991 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12991 ⟨19,by decide⟩).lower ∧ (cell12991 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12991 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12991 ⟨20,by decide⟩).lower ∧ (cell12991 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12991 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12991 ⟨21,by decide⟩).lower ∧ (cell12991 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12991 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12991 ⟨22,by decide⟩).lower ∧ (cell12991 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12991 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12991 ⟨23,by decide⟩).lower ∧ (cell12991 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12991 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12991 ⟨24,by decide⟩).lower ∧ (cell12991 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12991 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12991 ⟨25,by decide⟩).lower ∧ (cell12991 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12991 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12991 ⟨26,by decide⟩).lower ∧ (cell12991 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12991 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12991 ⟨27,by decide⟩).lower ∧ (cell12991 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12991 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12991 ⟨28,by decide⟩).lower ∧ (cell12991 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12991 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12991 ⟨29,by decide⟩).lower ∧ (cell12991 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12991 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12991 ⟨30,by decide⟩).lower ∧ (cell12991 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12991 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12991 ⟨31,by decide⟩).lower ∧ (cell12991 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12991 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12991 ⟨32,by decide⟩).lower ∧ (cell12991 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12991 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12991 ⟨33,by decide⟩).lower ∧ (cell12991 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12991 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12991 ⟨34,by decide⟩).lower ∧ (cell12991 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12991 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12991 ⟨35,by decide⟩).lower ∧ (cell12991 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12991 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12991 ⟨36,by decide⟩).lower ∧ (cell12991 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12991 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12991 ⟨37,by decide⟩).lower ∧ (cell12991 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12991 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12991 ⟨38,by decide⟩).lower ∧ (cell12991 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12991 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12991 ⟨39,by decide⟩).lower ∧ (cell12991 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12991 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12991 ⟨40,by decide⟩).lower ∧ (cell12991 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12991 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12991 ⟨41,by decide⟩).lower ∧ (cell12991 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12991 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12991 ⟨42,by decide⟩).lower ∧ (cell12991 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12991 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12991 ⟨43,by decide⟩).lower ∧ (cell12991 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12991 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12991 ⟨44,by decide⟩).lower ∧ (cell12991 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12991 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12991 ⟨45,by decide⟩).lower ∧ (cell12991 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12991 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12991 ⟨46,by decide⟩).lower ∧ (cell12991 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12991 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12991 ⟨47,by decide⟩).lower ∧ (cell12991 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12991 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12991 ⟨48,by decide⟩).lower ∧ (cell12991 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12991 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12991 ⟨49,by decide⟩).lower ∧ (cell12991 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12991 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12991 ⟨50,by decide⟩).lower ∧ (cell12991 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12991 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12991 ⟨51,by decide⟩).lower ∧ (cell12991 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12991 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12991 ⟨52,by decide⟩).lower ∧ (cell12991 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12991 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12991 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12991 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12991,cell12991,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12991 i).lower ∧
    (cell12991 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12991 i).upper ≤ (0.532 : ℝ) ∧
    (cell12991 i).centre ≤ (0.1 : ℝ) ∧ (cell12991 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12991 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12991 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12991

/-! The local source numeric instances at 12991 have no network premises. -/
namespace BstLean.Part269.N12991
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12991)
open BstLean.Part268 (cell12991)

noncomputable def sourceNumerics12991 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12991 (cell12991 i)
      scalarRow12991.M scalarRow12991.H scalarRow12991.xi := by
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
    energy_allowance := scalarRow12991.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12991]
    centre_nonneg := (scalarRow12991.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12991])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12991
/-! Actual 12992 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12992
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12992 ≤ (1.035401002091 : ℝ) := by
  have hr : (113.982454790200 : ℝ) ≤ √(12992 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.982454790200 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12992 12992 (11 / 1000) ≤
    (0.008386263906 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12992) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.982454790200 : ℝ) ≤ √(12992 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12992)
  have hdiv : K / √(12992 : ℝ) ≤ K / 113.982454790200 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.982454790200 ≤ (0.008386263906 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12992.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12992 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12992 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12992 := gPlus_lower 12992
end BstLean.Part269.N12992

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12992
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035401002090 : ℝ) ≤ wn 12992 := by
  have hn : √(12992 : ℝ) ≤ 113.982454790201 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12992 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.982454790201 ≤ 2 / √(12992 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246122717 : ℝ) ≤ rhoBar 12992 BstLean.Part154.csC ∧
    rhoBar 12992 BstLean.Part154.csC ≤ 0.000246123098 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035401002090 : ℝ) / (1.295212 * 12992) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035401002091 : ℝ) / (1.29521 * 12992) := by gcongr
      _ ≤ (0.000246123098 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12992 BstLean.Part154.csC) ≤ 0.000984552969 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12992 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12992 BstLean.Part154.csC) (piBar (rhoBar 12992 BstLean.Part154.csC)) ≤ 0.000187990283 ∧
    cc1 (rhoBar 12992 BstLean.Part154.csC) (piBar (rhoBar 12992 BstLean.Part154.csC)) ≤ 0.000119619506 ∧
    cc2 (rhoBar 12992 BstLean.Part154.csC) ≤ 0.000069440090 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12992 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12992 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12992 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12992 BstLean.Part154.csC * nuR (rhoBar 12992 BstLean.Part154.csC)) ≤ 0.000492261341 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246123098 : ℝ) * 0.000984552969 := by gcongr
      _ ≤ (0.000492261341 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12992 BstLean.Part154.csC) * nuR (rhoBar 12992 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000984552969 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12992 BstLean.Part154.csC) * rhoBar 12992 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246123098 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246123098 / 2 + 0.399 * 0.000984552969 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187990283 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492261341 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119619506 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246123098 / 1.414213562 := by gcongr
      _ ≤ (0.000069440090 : ℝ) := by norm_num

end BstLean.Part269.N12992

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12992
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12992 BstLean.Part154.csC) (piBar (rhoBar 12992 BstLean.Part154.csC)) ≤ 1.52618E-7 := by
  have hr0 : 0 ≤ rhoBar 12992 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12992 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12992 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12992 BstLean.Part154.csC) (piBar (rhoBar 12992 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12992 BstLean.Part154.csC) (piBar (rhoBar 12992 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12992 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187990283 : ℝ) ^ 2 + 0.000119619506 ^ 2 + 3 * 0.000069440090 ^ 2 +
        2 * 0.797885 * 0.000187990283 * 0.000119619506 + 2 * 0.000187990283 * 0.000069440090 +
        4 * 0.797885 * 0.000119619506 * 0.000069440090 := by gcongr
    _ ≤ (1.52618E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12992 BstLean.Part154.csC Θ ≤ 0.002568163266 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12992 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12992 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12992 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12992 BstLean.Part154.csC) (piBar (rhoBar 12992 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12992 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035401002091 * 1.52618E-7 / (0.000246122717 : ℝ) := by gcongr
    _ ≤ 0.002568163266 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12992 BstLean.Part154.csC Θ ≤ 0.002848395297 + 0.000648934941 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12992 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12992 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12992 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035401002091 : ℝ) * ((2 * Θ * 0.000246123098 +
        (6863 / 10000) * 0.000246123098 * 12992 * 0.000984552969) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002848395297 + 0.000648934941 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12992 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12992 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12992 0.011 Θ ∧ gammaRatio 12992 0.011 Θ ≤ 0.000084610757 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12992 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035401002091 : ℝ) * 0.525 / ((1 - 0.011) * 12992) := by gcongr
      _ ≤ (0.000084610757 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12992 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12992 0.011 Θ) :=
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
    badAllowance 12992 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12992 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12992 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12992 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12992 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12992 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 12992 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12992 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12992 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12992 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12992 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035401002091 : ℝ) * 12992 *
        (1.5230E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12992 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003270230520 + 0.003217098207 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12992

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12992
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12992 BstLean.Part154.csC) (piBar (rhoBar 12992 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12992 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12992 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12992 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12992 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12992 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12992 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12992 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12992 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12992 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12992 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12992 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12992 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12992 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12992 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051884799702 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12992) ≤ 0.010477380780 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12992 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035401002091)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010477380780 + 2 * 0.737676 / 12992) := by gcongr
    _ ≤ (0.051884799702 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12992 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12992

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12992
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516476608 : ℝ) ≤ plow 12992 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12992) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052465807079)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348285715) : eMP 12992 0.011 xi bn ≤ 0.001161139504 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12992 : ℝ) * (1 - 0.011))) ≤ 0.000574155825 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001348285715 / (12992 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574155825 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574155825 : ℝ) + 3.141593 * 0.052465807079 / (12992 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001161139504 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052465807079)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348285715) : PiBarMP 12992 12 0.011 xi bn ≤ 0.159410634693 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12992 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036719010268 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.353817756615 : ℝ) ≤ √((12992 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.982454790200 : ℝ) ≤ √(12992 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12992) ≤ 0.122232919869 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036719010268 + 0.052465807079 * 1.772454 / (2 * (113.353817756615 : ℝ))) * (1 + 0.001161139504) +
        8 / (12992 * 113.982454790200) + 0.122232919869 := by gcongr
    _ ≤ (0.159410634693 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052465807079)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348285715) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280938957226) :
    parallelOracle 12992 0.011 xi bn cd ≤ 0.160378808167 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12992 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12992 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516476608 : ℝ) ≤ plow 12992 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.982454790200 : ℝ) ≤ √(12992 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280938957226 : ℝ) / (2 * 0.560516476608 * 113.982454790200)) * 0.159410634693 +
        0.280938957226 ^ 2 / (2 * 0.560516476608 * 113.982454790200) := by gcongr
    _ ≤ (0.160378808167 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052465807079) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348285715)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280938957226) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12992 12992 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516476608 : ℝ) ≤ plow 12992 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.982454790200 : ℝ) ≤ √(12992 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12992 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12992 Θ 1.22 ≤ 0.011634251100 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.982454790200 := by gcongr <;> linarith
      _ ≤ (0.011634251100 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12992 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12992 12992 0.011 ≤ 0.008386263906 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12992 12992 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12992 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12992 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12992 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12992 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160378808167 + 0.011634251100 + (0.008386263906 : ℝ) *
        (1 + 2 * (0.280938957226 + 0.011634251100) / (0.560516476608 * 113.982454790200))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12992]

end BstLean.Part269.N12992

/-! The original eight local profiles supply actual 12992 moment certificates. -/
namespace BstLean.Part269.N12992
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12992 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12992 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12992 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052465807079 ∧
    0 ≤ bN 12992 BstLean.Part154.csC (groupTheta g) ∧ bN 12992 BstLean.Part154.csC (groupTheta g) ≤ 0.001348285715 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12992 12992 0.011
      (momentAllowance 12992 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12992 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12992 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12992 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12992 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12992 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229054157524 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12992 0.011
      (momentAllowance 12992 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12992 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12992
/-! The actual computed-centre upper energy formula at 12992. -/
namespace BstLean.Part269.N12992
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12992

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12992
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12992)
open BstLean.Part268 (cell12992)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084681089668
  | 2 => 0.085610040402
  | 3 => 0.086535242465
  | 4 => 0.087457670099
  | 5 => 0.088378514774
  | 6 => 0.089299219078
  | 7 => 0.090221514106
  | 8 => 0.091147460437
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12992 12992 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12992 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12992

/-! Actual upper energy certificates on all 43 source endpoints at 12992. -/
namespace BstLean.Part269.N12992
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12992)
open BstLean.Part268 (cell12992)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12992 (gMinus 12992) (1 - (cell12992 i).lower) ≤ 1 ∧
    energyUpper 12992 (gMinus 12992) (BstLean.Part211.gPlus 12992)
      (finiteEnergy 12992 12992 0.011) (1 - (cell12992 i).lower) ≤
      (cell12992 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨10,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨11,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨12,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨13,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨14,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨15,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨16,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨17,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨18,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨19,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨20,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨21,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨22,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨23,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨24,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨25,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨26,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨27,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨28,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨29,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨30,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨31,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨32,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨33,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨34,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨35,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨36,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨37,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨38,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨39,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨40,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨41,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨42,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨43,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨44,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨45,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨46,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨47,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨48,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨49,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨50,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨51,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12992) (by norm_num)
        (q := 1 - (cell12992 ⟨52,by decide⟩).lower)
        (by norm_num [cell12992]) (by norm_num [cell12992])
      exact ⟨E.1,E.2.trans (by norm_num [cell12992])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12992

/-! Source-cell containment and simple scalar guards at 12992. -/
namespace BstLean.Part269.N12992
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12992)
open BstLean.Part268 (cell12992)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12992 ⟨10,by decide⟩).lower ∧ (cell12992 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12992 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12992 ⟨11,by decide⟩).lower ∧ (cell12992 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12992 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12992 ⟨12,by decide⟩).lower ∧ (cell12992 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12992 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12992 ⟨13,by decide⟩).lower ∧ (cell12992 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12992 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12992 ⟨14,by decide⟩).lower ∧ (cell12992 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12992 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12992 ⟨15,by decide⟩).lower ∧ (cell12992 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12992 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12992 ⟨16,by decide⟩).lower ∧ (cell12992 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12992 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12992 ⟨17,by decide⟩).lower ∧ (cell12992 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12992 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12992 ⟨18,by decide⟩).lower ∧ (cell12992 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12992 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12992 ⟨19,by decide⟩).lower ∧ (cell12992 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12992 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12992 ⟨20,by decide⟩).lower ∧ (cell12992 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12992 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12992 ⟨21,by decide⟩).lower ∧ (cell12992 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12992 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12992 ⟨22,by decide⟩).lower ∧ (cell12992 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12992 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12992 ⟨23,by decide⟩).lower ∧ (cell12992 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12992 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12992 ⟨24,by decide⟩).lower ∧ (cell12992 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12992 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12992 ⟨25,by decide⟩).lower ∧ (cell12992 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12992 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12992 ⟨26,by decide⟩).lower ∧ (cell12992 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12992 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12992 ⟨27,by decide⟩).lower ∧ (cell12992 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12992 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12992 ⟨28,by decide⟩).lower ∧ (cell12992 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12992 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12992 ⟨29,by decide⟩).lower ∧ (cell12992 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12992 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12992 ⟨30,by decide⟩).lower ∧ (cell12992 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12992 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12992 ⟨31,by decide⟩).lower ∧ (cell12992 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12992 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12992 ⟨32,by decide⟩).lower ∧ (cell12992 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12992 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12992 ⟨33,by decide⟩).lower ∧ (cell12992 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12992 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12992 ⟨34,by decide⟩).lower ∧ (cell12992 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12992 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12992 ⟨35,by decide⟩).lower ∧ (cell12992 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12992 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12992 ⟨36,by decide⟩).lower ∧ (cell12992 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12992 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12992 ⟨37,by decide⟩).lower ∧ (cell12992 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12992 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12992 ⟨38,by decide⟩).lower ∧ (cell12992 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12992 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12992 ⟨39,by decide⟩).lower ∧ (cell12992 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12992 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12992 ⟨40,by decide⟩).lower ∧ (cell12992 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12992 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12992 ⟨41,by decide⟩).lower ∧ (cell12992 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12992 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12992 ⟨42,by decide⟩).lower ∧ (cell12992 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12992 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12992 ⟨43,by decide⟩).lower ∧ (cell12992 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12992 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12992 ⟨44,by decide⟩).lower ∧ (cell12992 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12992 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12992 ⟨45,by decide⟩).lower ∧ (cell12992 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12992 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12992 ⟨46,by decide⟩).lower ∧ (cell12992 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12992 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12992 ⟨47,by decide⟩).lower ∧ (cell12992 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12992 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12992 ⟨48,by decide⟩).lower ∧ (cell12992 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12992 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12992 ⟨49,by decide⟩).lower ∧ (cell12992 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12992 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12992 ⟨50,by decide⟩).lower ∧ (cell12992 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12992 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12992 ⟨51,by decide⟩).lower ∧ (cell12992 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12992 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12992 ⟨52,by decide⟩).lower ∧ (cell12992 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12992 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12992 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12992 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12992,cell12992,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12992 i).lower ∧
    (cell12992 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12992 i).upper ≤ (0.532 : ℝ) ∧
    (cell12992 i).centre ≤ (0.1 : ℝ) ∧ (cell12992 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12992 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12992 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12992

/-! The local source numeric instances at 12992 have no network premises. -/
namespace BstLean.Part269.N12992
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12992)
open BstLean.Part268 (cell12992)

noncomputable def sourceNumerics12992 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12992 (cell12992 i)
      scalarRow12992.M scalarRow12992.H scalarRow12992.xi := by
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
    energy_allowance := scalarRow12992.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12992]
    centre_nonneg := (scalarRow12992.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12992])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12992
/-! Actual 12993 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12993
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12993 ≤ (1.035399627907 : ℝ) := by
  have hr : (113.986841345832 : ℝ) ≤ √(12993 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.986841345832 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12993 12993 (11 / 1000) ≤
    (0.008385941175 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12993) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.986841345832 : ℝ) ≤ √(12993 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12993)
  have hdiv : K / √(12993 : ℝ) ≤ K / 113.986841345832 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.986841345832 ≤ (0.008385941175 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12993.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12993 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12993 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12993 := gPlus_lower 12993
end BstLean.Part269.N12993

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12993
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035399627906 : ℝ) ≤ wn 12993 := by
  have hn : √(12993 : ℝ) ≤ 113.986841345833 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12993 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.986841345833 ≤ 2 / √(12993 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246103447 : ℝ) ≤ rhoBar 12993 BstLean.Part154.csC ∧
    rhoBar 12993 BstLean.Part154.csC ≤ 0.000246103828 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035399627906 : ℝ) / (1.295212 * 12993) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035399627907 : ℝ) / (1.29521 * 12993) := by gcongr
      _ ≤ (0.000246103828 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12993 BstLean.Part154.csC) ≤ 0.000984475880 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12993 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12993 BstLean.Part154.csC) (piBar (rhoBar 12993 BstLean.Part154.csC)) ≤ 0.000187975564 ∧
    cc1 (rhoBar 12993 BstLean.Part154.csC) (piBar (rhoBar 12993 BstLean.Part154.csC)) ≤ 0.000119610140 ∧
    cc2 (rhoBar 12993 BstLean.Part154.csC) ≤ 0.000069434653 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12993 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12993 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12993 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12993 BstLean.Part154.csC * nuR (rhoBar 12993 BstLean.Part154.csC)) ≤ 0.000492222798 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246103828 : ℝ) * 0.000984475880 := by gcongr
      _ ≤ (0.000492222798 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12993 BstLean.Part154.csC) * nuR (rhoBar 12993 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000984475880 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12993 BstLean.Part154.csC) * rhoBar 12993 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246103828 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246103828 / 2 + 0.399 * 0.000984475880 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187975564 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492222798 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119610140 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246103828 / 1.414213562 := by gcongr
      _ ≤ (0.000069434653 : ℝ) := by norm_num

end BstLean.Part269.N12993

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12993
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12993 BstLean.Part154.csC) (piBar (rhoBar 12993 BstLean.Part154.csC)) ≤ 1.52594E-7 := by
  have hr0 : 0 ≤ rhoBar 12993 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12993 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12993 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12993 BstLean.Part154.csC) (piBar (rhoBar 12993 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12993 BstLean.Part154.csC) (piBar (rhoBar 12993 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12993 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187975564 : ℝ) ^ 2 + 0.000119610140 ^ 2 + 3 * 0.000069434653 ^ 2 +
        2 * 0.797885 * 0.000187975564 * 0.000119610140 + 2 * 0.000187975564 * 0.000069434653 +
        4 * 0.797885 * 0.000119610140 * 0.000069434653 := by gcongr
    _ ≤ (1.52594E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12993 BstLean.Part154.csC Θ ≤ 0.002567957057 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12993 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12993 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12993 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12993 BstLean.Part154.csC) (piBar (rhoBar 12993 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12993 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035399627907 * 1.52594E-7 / (0.000246103447 : ℝ) := by gcongr
    _ ≤ 0.002567957057 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12993 BstLean.Part154.csC Θ ≤ 0.002848164704 + 0.000648883272 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12993 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12993 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12993 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035399627907 : ℝ) * ((2 * Θ * 0.000246103828 +
        (6863 / 10000) * 0.000246103828 * 12993 * 0.000984475880) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002848164704 + 0.000648883272 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12993 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12993 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12993 0.011 Θ ∧ gammaRatio 12993 0.011 Θ ≤ 0.000084604132 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12993 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035399627907 : ℝ) * 0.525 / ((1 - 0.011) * 12993) := by gcongr
      _ ≤ (0.000084604132 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12993 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12993 0.011 Θ) :=
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
    badAllowance 12993 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12993 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12993 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12993 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12993 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12993 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 12993 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12993 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12993 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12993 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12993 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035399627907 : ℝ) * 12993 *
        (1.5230E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12993 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003269999927 + 0.003216840329 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12993

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12993
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12993 BstLean.Part154.csC) (piBar (rhoBar 12993 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12993 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12993 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12993 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12993 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12993 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12993 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12993 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12993 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12993 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12993 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12993 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12993 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12993 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12993 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051882781612 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12993) ≤ 0.010476977579 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12993 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035399627907)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010476977579 + 2 * 0.737676 / 12993) := by gcongr
    _ ≤ (0.051882781612 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12993 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12993

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12993
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516519818 : ℝ) ≤ plow 12993 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12993) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052465441100)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348177455) : eMP 12993 0.011 xi bn ≤ 0.001161048137 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12993 : ℝ) * (1 - 0.011))) ≤ 0.000574110680 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001348177455 / (12993 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574110680 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574110680 : ℝ) + 3.141593 * 0.052465441100 / (12993 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001161048137 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052465441100)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348177455) : PiBarMP 12993 12 0.011 xi bn ≤ 0.159404432210 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12993 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036717536070 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.358180119477 : ℝ) ≤ √((12993 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.986841345832 : ℝ) ≤ √(12993 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12993) ≤ 0.122228215979 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036717536070 + 0.052465441100 * 1.772454 / (2 * (113.358180119477 : ℝ))) * (1 + 0.001161048137) +
        8 / (12993 * 113.986841345832) + 0.122228215979 := by gcongr
    _ ≤ (0.159404432210 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052465441100)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348177455) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280936140243) :
    parallelOracle 12993 0.011 xi bn cd ≤ 0.160372538814 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12993 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12993 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516519818 : ℝ) ≤ plow 12993 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.986841345832 : ℝ) ≤ √(12993 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280936140243 : ℝ) / (2 * 0.560516519818 * 113.986841345832)) * 0.159404432210 +
        0.280936140243 ^ 2 / (2 * 0.560516519818 * 113.986841345832) := by gcongr
    _ ≤ (0.160372538814 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052465441100) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348177455)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280936140243) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12993 12993 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516519818 : ℝ) ≤ plow 12993 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.986841345832 : ℝ) ≤ √(12993 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12993 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12993 Θ 1.22 ≤ 0.011633803379 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.986841345832 := by gcongr <;> linarith
      _ ≤ (0.011633803379 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12993 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12993 12993 0.011 ≤ 0.008385941175 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12993 12993 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12993 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12993 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12993 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12993 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160372538814 + 0.011633803379 + (0.008385941175 : ℝ) *
        (1 + 2 * (0.280936140243 + 0.011633803379) / (0.560516519818 * 113.986841345832))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12993]

end BstLean.Part269.N12993

/-! The original eight local profiles supply actual 12993 moment certificates. -/
namespace BstLean.Part269.N12993
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12993 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12993 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12993 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052465441100 ∧
    0 ≤ bN 12993 BstLean.Part154.csC (groupTheta g) ∧ bN 12993 BstLean.Part154.csC (groupTheta g) ≤ 0.001348177455 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12993 12993 0.011
      (momentAllowance 12993 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12993 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12993 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12993 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12993 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12993 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229053358631 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12993 0.011
      (momentAllowance 12993 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12993 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12993
/-! The actual computed-centre upper energy formula at 12993. -/
namespace BstLean.Part269.N12993
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12993

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12993
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12993)
open BstLean.Part268 (cell12993)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084678464976
  | 2 => 0.085607380933
  | 3 => 0.086532542907
  | 4 => 0.087454923899
  | 5 => 0.088375713911
  | 6 => 0.089296353807
  | 7 => 0.090218572669
  | 8 => 0.091144428746
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12993 12993 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12993 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12993

/-! Actual upper energy certificates on all 43 source endpoints at 12993. -/
namespace BstLean.Part269.N12993
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12993)
open BstLean.Part268 (cell12993)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12993 (gMinus 12993) (1 - (cell12993 i).lower) ≤ 1 ∧
    energyUpper 12993 (gMinus 12993) (BstLean.Part211.gPlus 12993)
      (finiteEnergy 12993 12993 0.011) (1 - (cell12993 i).lower) ≤
      (cell12993 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨10,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨11,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨12,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨13,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨14,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨15,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨16,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨17,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨18,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨19,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨20,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨21,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨22,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨23,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨24,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨25,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨26,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨27,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨28,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨29,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨30,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨31,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨32,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨33,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨34,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨35,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨36,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨37,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨38,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨39,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨40,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨41,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨42,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨43,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨44,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨45,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨46,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨47,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨48,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨49,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨50,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨51,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12993) (by norm_num)
        (q := 1 - (cell12993 ⟨52,by decide⟩).lower)
        (by norm_num [cell12993]) (by norm_num [cell12993])
      exact ⟨E.1,E.2.trans (by norm_num [cell12993])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12993

/-! Source-cell containment and simple scalar guards at 12993. -/
namespace BstLean.Part269.N12993
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12993)
open BstLean.Part268 (cell12993)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12993 ⟨10,by decide⟩).lower ∧ (cell12993 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12993 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12993 ⟨11,by decide⟩).lower ∧ (cell12993 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12993 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12993 ⟨12,by decide⟩).lower ∧ (cell12993 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12993 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12993 ⟨13,by decide⟩).lower ∧ (cell12993 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12993 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12993 ⟨14,by decide⟩).lower ∧ (cell12993 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12993 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12993 ⟨15,by decide⟩).lower ∧ (cell12993 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12993 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12993 ⟨16,by decide⟩).lower ∧ (cell12993 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12993 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12993 ⟨17,by decide⟩).lower ∧ (cell12993 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12993 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12993 ⟨18,by decide⟩).lower ∧ (cell12993 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12993 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12993 ⟨19,by decide⟩).lower ∧ (cell12993 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12993 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12993 ⟨20,by decide⟩).lower ∧ (cell12993 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12993 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12993 ⟨21,by decide⟩).lower ∧ (cell12993 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12993 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12993 ⟨22,by decide⟩).lower ∧ (cell12993 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12993 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12993 ⟨23,by decide⟩).lower ∧ (cell12993 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12993 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12993 ⟨24,by decide⟩).lower ∧ (cell12993 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12993 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12993 ⟨25,by decide⟩).lower ∧ (cell12993 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12993 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12993 ⟨26,by decide⟩).lower ∧ (cell12993 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12993 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12993 ⟨27,by decide⟩).lower ∧ (cell12993 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12993 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12993 ⟨28,by decide⟩).lower ∧ (cell12993 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12993 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12993 ⟨29,by decide⟩).lower ∧ (cell12993 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12993 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12993 ⟨30,by decide⟩).lower ∧ (cell12993 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12993 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12993 ⟨31,by decide⟩).lower ∧ (cell12993 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12993 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12993 ⟨32,by decide⟩).lower ∧ (cell12993 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12993 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12993 ⟨33,by decide⟩).lower ∧ (cell12993 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12993 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12993 ⟨34,by decide⟩).lower ∧ (cell12993 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12993 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12993 ⟨35,by decide⟩).lower ∧ (cell12993 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12993 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12993 ⟨36,by decide⟩).lower ∧ (cell12993 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12993 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12993 ⟨37,by decide⟩).lower ∧ (cell12993 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12993 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12993 ⟨38,by decide⟩).lower ∧ (cell12993 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12993 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12993 ⟨39,by decide⟩).lower ∧ (cell12993 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12993 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12993 ⟨40,by decide⟩).lower ∧ (cell12993 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12993 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12993 ⟨41,by decide⟩).lower ∧ (cell12993 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12993 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12993 ⟨42,by decide⟩).lower ∧ (cell12993 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12993 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12993 ⟨43,by decide⟩).lower ∧ (cell12993 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12993 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12993 ⟨44,by decide⟩).lower ∧ (cell12993 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12993 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12993 ⟨45,by decide⟩).lower ∧ (cell12993 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12993 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12993 ⟨46,by decide⟩).lower ∧ (cell12993 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12993 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12993 ⟨47,by decide⟩).lower ∧ (cell12993 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12993 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12993 ⟨48,by decide⟩).lower ∧ (cell12993 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12993 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12993 ⟨49,by decide⟩).lower ∧ (cell12993 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12993 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12993 ⟨50,by decide⟩).lower ∧ (cell12993 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12993 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12993 ⟨51,by decide⟩).lower ∧ (cell12993 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12993 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12993 ⟨52,by decide⟩).lower ∧ (cell12993 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12993 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12993 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12993 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12993,cell12993,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12993 i).lower ∧
    (cell12993 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12993 i).upper ≤ (0.532 : ℝ) ∧
    (cell12993 i).centre ≤ (0.1 : ℝ) ∧ (cell12993 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12993 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12993 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12993

/-! The local source numeric instances at 12993 have no network premises. -/
namespace BstLean.Part269.N12993
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12993)
open BstLean.Part268 (cell12993)

noncomputable def sourceNumerics12993 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12993 (cell12993 i)
      scalarRow12993.M scalarRow12993.H scalarRow12993.xi := by
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
    energy_allowance := scalarRow12993.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12993]
    centre_nonneg := (scalarRow12993.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12993])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12993
/-! Actual 12994 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12994
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12994 ≤ (1.035398253882 : ℝ) := by
  have hr : (113.991227732663 : ℝ) ≤ √(12994 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.991227732663 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12994 12994 (11 / 1000) ≤
    (0.008385618481 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12994) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.991227732663 : ℝ) ≤ √(12994 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12994)
  have hdiv : K / √(12994 : ℝ) ≤ K / 113.991227732663 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.991227732663 ≤ (0.008385618481 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12994.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12994 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12994 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12994 := gPlus_lower 12994
end BstLean.Part269.N12994

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12994
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035398253881 : ℝ) ≤ wn 12994 := by
  have hn : √(12994 : ℝ) ≤ 113.991227732664 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12994 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.991227732664 ≤ 2 / √(12994 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246084181 : ℝ) ≤ rhoBar 12994 BstLean.Part154.csC ∧
    rhoBar 12994 BstLean.Part154.csC ≤ 0.000246084562 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035398253881 : ℝ) / (1.295212 * 12994) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035398253882 : ℝ) / (1.29521 * 12994) := by gcongr
      _ ≤ (0.000246084562 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12994 BstLean.Part154.csC) ≤ 0.000984398806 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12994 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12994 BstLean.Part154.csC) (piBar (rhoBar 12994 BstLean.Part154.csC)) ≤ 0.000187960847 ∧
    cc1 (rhoBar 12994 BstLean.Part154.csC) (piBar (rhoBar 12994 BstLean.Part154.csC)) ≤ 0.000119600777 ∧
    cc2 (rhoBar 12994 BstLean.Part154.csC) ≤ 0.000069429217 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12994 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12994 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12994 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12994 BstLean.Part154.csC * nuR (rhoBar 12994 BstLean.Part154.csC)) ≤ 0.000492184264 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246084562 : ℝ) * 0.000984398806 := by gcongr
      _ ≤ (0.000492184264 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12994 BstLean.Part154.csC) * nuR (rhoBar 12994 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000984398806 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12994 BstLean.Part154.csC) * rhoBar 12994 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246084562 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246084562 / 2 + 0.399 * 0.000984398806 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187960847 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492184264 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119600777 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246084562 / 1.414213562 := by gcongr
      _ ≤ (0.000069429217 : ℝ) := by norm_num

end BstLean.Part269.N12994

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12994
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12994 BstLean.Part154.csC) (piBar (rhoBar 12994 BstLean.Part154.csC)) ≤ 1.52571E-7 := by
  have hr0 : 0 ≤ rhoBar 12994 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12994 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12994 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12994 BstLean.Part154.csC) (piBar (rhoBar 12994 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12994 BstLean.Part154.csC) (piBar (rhoBar 12994 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12994 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187960847 : ℝ) ^ 2 + 0.000119600777 ^ 2 + 3 * 0.000069429217 ^ 2 +
        2 * 0.797885 * 0.000187960847 * 0.000119600777 + 2 * 0.000187960847 * 0.000069429217 +
        4 * 0.797885 * 0.000119600777 * 0.000069429217 := by gcongr
    _ ≤ (1.52571E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12994 BstLean.Part154.csC Θ ≤ 0.002567767605 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12994 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12994 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12994 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12994 BstLean.Part154.csC) (piBar (rhoBar 12994 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12994 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035398253882 * 1.52571E-7 / (0.000246084181 : ℝ) := by gcongr
    _ ≤ 0.002567767605 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12994 BstLean.Part154.csC Θ ≤ 0.002847934169 + 0.000648831614 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12994 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12994 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12994 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035398253882 : ℝ) * ((2 * Θ * 0.000246084562 +
        (6863 / 10000) * 0.000246084562 * 12994 * 0.000984398806) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002847934169 + 0.000648831614 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12994 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12994 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12994 0.011 Θ ∧ gammaRatio 12994 0.011 Θ ≤ 0.000084597509 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12994 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035398253882 : ℝ) * 0.525 / ((1 - 0.011) * 12994) := by gcongr
      _ ≤ (0.000084597509 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12994 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12994 0.011 Θ) :=
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
    badAllowance 12994 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12994 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12994 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12994 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12994 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12994 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 12994 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12994 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12994 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12994 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12994 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035398253882 : ℝ) * 12994 *
        (1.5230E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12994 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003269769392 + 0.003216599219 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12994

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12994
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12994 BstLean.Part154.csC) (piBar (rhoBar 12994 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12994 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12994 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12994 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12994 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12994 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12994 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12994 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12994 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12994 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12994 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12994 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12994 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12994 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12994 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051880763758 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12994) ≤ 0.010476574425 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12994 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035398253882)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010476574425 + 2 * 0.737676 / 12994) := by gcongr
    _ ≤ (0.051880763758 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12994 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12994

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12994
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516563021 : ℝ) ≤ plow 12994 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12994) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052465083982)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348077993) : eMP 12994 0.011 xi bn ≤ 0.001160960524 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12994 : ℝ) * (1 - 0.011))) ≤ 0.000574067411 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001348077993 / (12994 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574067411 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574067411 : ℝ) + 3.141593 * 0.052465083982 / (12994 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001160960524 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052465083982)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348077993) : PiBarMP 12994 12 0.011 xi bn ≤ 0.159398350372 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12994 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036716181624 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.362542314469 : ℝ) ≤ √((12994 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.991227732663 : ℝ) ≤ √(12994 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12994) ≤ 0.122223512633 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036716181624 + 0.052465083982 * 1.772454 / (2 * (113.362542314469 : ℝ))) * (1 + 0.001160960524) +
        8 / (12994 * 113.991227732663) + 0.122223512633 := by gcongr
    _ ≤ (0.159398350372 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052465083982)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348077993) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280933342836) :
    parallelOracle 12994 0.011 xi bn cd ≤ 0.160366390488 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12994 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12994 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516563021 : ℝ) ≤ plow 12994 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.991227732663 : ℝ) ≤ √(12994 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280933342836 : ℝ) / (2 * 0.560516563021 * 113.991227732663)) * 0.159398350372 +
        0.280933342836 ^ 2 / (2 * 0.560516563021 * 113.991227732663) := by gcongr
    _ ≤ (0.160366390488 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052465083982) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001348077993)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280933342836) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12994 12994 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516563021 : ℝ) ≤ plow 12994 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.991227732663 : ℝ) ≤ √(12994 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12994 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12994 Θ 1.22 ≤ 0.011633355710 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.991227732663 := by gcongr <;> linarith
      _ ≤ (0.011633355710 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12994 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12994 12994 0.011 ≤ 0.008385618481 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12994 12994 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12994 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12994 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12994 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12994 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160366390488 + 0.011633355710 + (0.008385618481 : ℝ) *
        (1 + 2 * (0.280933342836 + 0.011633355710) / (0.560516563021 * 113.991227732663))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12994]

end BstLean.Part269.N12994

/-! The original eight local profiles supply actual 12994 moment certificates. -/
namespace BstLean.Part269.N12994
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12994 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12994 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12994 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052465083982 ∧
    0 ≤ bN 12994 BstLean.Part154.csC (groupTheta g) ∧ bN 12994 BstLean.Part154.csC (groupTheta g) ≤ 0.001348077993 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12994 12994 0.011
      (momentAllowance 12994 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12994 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12994 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12994 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12994 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12994 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229052579078 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12994 0.011
      (momentAllowance 12994 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12994 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12994
/-! The actual computed-centre upper energy formula at 12994. -/
namespace BstLean.Part269.N12994
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12994

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12994
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12994)
open BstLean.Part268 (cell12994)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084675841096
  | 2 => 0.085604722305
  | 3 => 0.086529844227
  | 4 => 0.087452178621
  | 5 => 0.088372914024
  | 6 => 0.089293489577
  | 7 => 0.090215632354
  | 8 => 0.091141398274
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12994 12994 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12994 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12994

/-! Actual upper energy certificates on all 43 source endpoints at 12994. -/
namespace BstLean.Part269.N12994
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12994)
open BstLean.Part268 (cell12994)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12994 (gMinus 12994) (1 - (cell12994 i).lower) ≤ 1 ∧
    energyUpper 12994 (gMinus 12994) (BstLean.Part211.gPlus 12994)
      (finiteEnergy 12994 12994 0.011) (1 - (cell12994 i).lower) ≤
      (cell12994 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨10,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨11,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨12,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨13,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨14,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨15,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨16,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨17,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨18,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨19,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨20,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨21,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨22,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨23,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨24,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨25,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨26,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨27,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨28,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨29,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨30,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨31,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨32,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨33,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨34,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨35,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨36,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨37,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨38,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨39,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨40,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨41,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨42,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨43,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨44,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨45,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨46,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨47,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨48,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨49,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨50,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨51,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12994) (by norm_num)
        (q := 1 - (cell12994 ⟨52,by decide⟩).lower)
        (by norm_num [cell12994]) (by norm_num [cell12994])
      exact ⟨E.1,E.2.trans (by norm_num [cell12994])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12994

/-! Source-cell containment and simple scalar guards at 12994. -/
namespace BstLean.Part269.N12994
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12994)
open BstLean.Part268 (cell12994)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12994 ⟨10,by decide⟩).lower ∧ (cell12994 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12994 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12994 ⟨11,by decide⟩).lower ∧ (cell12994 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12994 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12994 ⟨12,by decide⟩).lower ∧ (cell12994 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12994 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12994 ⟨13,by decide⟩).lower ∧ (cell12994 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12994 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12994 ⟨14,by decide⟩).lower ∧ (cell12994 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12994 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12994 ⟨15,by decide⟩).lower ∧ (cell12994 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12994 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12994 ⟨16,by decide⟩).lower ∧ (cell12994 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12994 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12994 ⟨17,by decide⟩).lower ∧ (cell12994 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12994 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12994 ⟨18,by decide⟩).lower ∧ (cell12994 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12994 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12994 ⟨19,by decide⟩).lower ∧ (cell12994 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12994 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12994 ⟨20,by decide⟩).lower ∧ (cell12994 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12994 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12994 ⟨21,by decide⟩).lower ∧ (cell12994 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12994 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12994 ⟨22,by decide⟩).lower ∧ (cell12994 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12994 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12994 ⟨23,by decide⟩).lower ∧ (cell12994 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12994 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12994 ⟨24,by decide⟩).lower ∧ (cell12994 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12994 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12994 ⟨25,by decide⟩).lower ∧ (cell12994 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12994 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12994 ⟨26,by decide⟩).lower ∧ (cell12994 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12994 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12994 ⟨27,by decide⟩).lower ∧ (cell12994 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12994 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12994 ⟨28,by decide⟩).lower ∧ (cell12994 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12994 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12994 ⟨29,by decide⟩).lower ∧ (cell12994 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12994 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12994 ⟨30,by decide⟩).lower ∧ (cell12994 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12994 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12994 ⟨31,by decide⟩).lower ∧ (cell12994 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12994 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12994 ⟨32,by decide⟩).lower ∧ (cell12994 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12994 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12994 ⟨33,by decide⟩).lower ∧ (cell12994 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12994 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12994 ⟨34,by decide⟩).lower ∧ (cell12994 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12994 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12994 ⟨35,by decide⟩).lower ∧ (cell12994 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12994 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12994 ⟨36,by decide⟩).lower ∧ (cell12994 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12994 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12994 ⟨37,by decide⟩).lower ∧ (cell12994 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12994 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12994 ⟨38,by decide⟩).lower ∧ (cell12994 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12994 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12994 ⟨39,by decide⟩).lower ∧ (cell12994 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12994 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12994 ⟨40,by decide⟩).lower ∧ (cell12994 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12994 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12994 ⟨41,by decide⟩).lower ∧ (cell12994 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12994 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12994 ⟨42,by decide⟩).lower ∧ (cell12994 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12994 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12994 ⟨43,by decide⟩).lower ∧ (cell12994 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12994 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12994 ⟨44,by decide⟩).lower ∧ (cell12994 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12994 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12994 ⟨45,by decide⟩).lower ∧ (cell12994 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12994 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12994 ⟨46,by decide⟩).lower ∧ (cell12994 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12994 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12994 ⟨47,by decide⟩).lower ∧ (cell12994 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12994 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12994 ⟨48,by decide⟩).lower ∧ (cell12994 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12994 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12994 ⟨49,by decide⟩).lower ∧ (cell12994 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12994 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12994 ⟨50,by decide⟩).lower ∧ (cell12994 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12994 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12994 ⟨51,by decide⟩).lower ∧ (cell12994 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12994 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12994 ⟨52,by decide⟩).lower ∧ (cell12994 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12994 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12994 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12994 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12994,cell12994,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12994 i).lower ∧
    (cell12994 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12994 i).upper ≤ (0.532 : ℝ) ∧
    (cell12994 i).centre ≤ (0.1 : ℝ) ∧ (cell12994 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12994 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12994 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12994

/-! The local source numeric instances at 12994 have no network premises. -/
namespace BstLean.Part269.N12994
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12994)
open BstLean.Part268 (cell12994)

noncomputable def sourceNumerics12994 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12994 (cell12994 i)
      scalarRow12994.M scalarRow12994.H scalarRow12994.xi := by
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
    energy_allowance := scalarRow12994.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12994]
    centre_nonneg := (scalarRow12994.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12994])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12994
/-! Actual 12995 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12995
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12995 ≤ (1.035396880016 : ℝ) := by
  have hr : (113.995613950713 : ℝ) ≤ √(12995 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.995613950713 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12995 12995 (11 / 1000) ≤
    (0.008385295825 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12995) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.995613950713 : ℝ) ≤ √(12995 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12995)
  have hdiv : K / √(12995 : ℝ) ≤ K / 113.995613950713 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.995613950713 ≤ (0.008385295825 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12995.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12995 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12995 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12995 := gPlus_lower 12995
end BstLean.Part269.N12995

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12995
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035396880015 : ℝ) ≤ wn 12995 := by
  have hn : √(12995 : ℝ) ≤ 113.995613950714 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12995 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.995613950714 ≤ 2 / √(12995 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246064918 : ℝ) ≤ rhoBar 12995 BstLean.Part154.csC ∧
    rhoBar 12995 BstLean.Part154.csC ≤ 0.000246065299 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035396880015 : ℝ) / (1.295212 * 12995) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035396880016 : ℝ) / (1.29521 * 12995) := by gcongr
      _ ≤ (0.000246065299 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12995 BstLean.Part154.csC) ≤ 0.000984321745 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12995 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12995 BstLean.Part154.csC) (piBar (rhoBar 12995 BstLean.Part154.csC)) ≤ 0.000187946134 ∧
    cc1 (rhoBar 12995 BstLean.Part154.csC) (piBar (rhoBar 12995 BstLean.Part154.csC)) ≤ 0.000119591414 ∧
    cc2 (rhoBar 12995 BstLean.Part154.csC) ≤ 0.000069423783 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12995 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12995 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12995 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12995 BstLean.Part154.csC * nuR (rhoBar 12995 BstLean.Part154.csC)) ≤ 0.000492145736 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246065299 : ℝ) * 0.000984321745 := by gcongr
      _ ≤ (0.000492145736 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12995 BstLean.Part154.csC) * nuR (rhoBar 12995 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000984321745 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12995 BstLean.Part154.csC) * rhoBar 12995 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246065299 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246065299 / 2 + 0.399 * 0.000984321745 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187946134 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492145736 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119591414 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246065299 / 1.414213562 := by gcongr
      _ ≤ (0.000069423783 : ℝ) := by norm_num

end BstLean.Part269.N12995

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12995
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12995 BstLean.Part154.csC) (piBar (rhoBar 12995 BstLean.Part154.csC)) ≤ 1.52547E-7 := by
  have hr0 : 0 ≤ rhoBar 12995 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12995 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12995 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12995 BstLean.Part154.csC) (piBar (rhoBar 12995 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12995 BstLean.Part154.csC) (piBar (rhoBar 12995 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12995 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187946134 : ℝ) ^ 2 + 0.000119591414 ^ 2 + 3 * 0.000069423783 ^ 2 +
        2 * 0.797885 * 0.000187946134 * 0.000119591414 + 2 * 0.000187946134 * 0.000069423783 +
        4 * 0.797885 * 0.000119591414 * 0.000069423783 := by gcongr
    _ ≤ (1.52547E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12995 BstLean.Part154.csC Θ ≤ 0.002567561263 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12995 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12995 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12995 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12995 BstLean.Part154.csC) (piBar (rhoBar 12995 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12995 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035396880016 * 1.52547E-7 / (0.000246064918 : ℝ) := by gcongr
    _ ≤ 0.002567561263 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12995 BstLean.Part154.csC Θ ≤ 0.002847703673 + 0.000648779964 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12995 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12995 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12995 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035396880016 : ℝ) * ((2 * Θ * 0.000246065299 +
        (6863 / 10000) * 0.000246065299 * 12995 * 0.000984321745) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002847703673 + 0.000648779964 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12995 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12995 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12995 0.011 Θ ∧ gammaRatio 12995 0.011 Θ ≤ 0.000084590887 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12995 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035396880016 : ℝ) * 0.525 / ((1 - 0.011) * 12995) := by gcongr
      _ ≤ (0.000084590887 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12995 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12995 0.011 Θ) :=
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
    badAllowance 12995 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12995 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 12995 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12995 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12995 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12995 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 12995 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12995 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12995 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12995 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12995 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035396880016 : ℝ) * 12995 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12995 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003269538896 + 0.003216341227 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12995

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12995
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12995 BstLean.Part154.csC) (piBar (rhoBar 12995 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12995 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12995 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12995 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12995 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12995 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12995 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12995 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12995 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12995 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12995 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12995 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12995 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12995 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12995 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051878746136 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12995) ≤ 0.010476171317 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12995 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035396880016)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010476171317 + 2 * 0.737676 / 12995) := by gcongr
    _ ≤ (0.051878746136 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12995 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12995

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12995
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516606217 : ℝ) ≤ plow 12995 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12995) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052464718041)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347969664) : eMP 12995 0.011 xi bn ≤ 0.001160869140 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12995 : ℝ) * (1 - 0.011))) ≤ 0.000574022257 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001347969664 / (12995 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574022257 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574022257 : ℝ) + 3.141593 * 0.052464718041 / (12995 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001160869140 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052464718041)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347969664) : PiBarMP 12995 12 0.011 xi bn ≤ 0.159392147924 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12995 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036714706373 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.366904341611 : ℝ) ≤ √((12995 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.995613950713 : ℝ) ≤ √(12995 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12995) ≤ 0.122218809829 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036714706373 + 0.052464718041 * 1.772454 / (2 * (113.366904341611 : ℝ))) * (1 + 0.001160869140) +
        8 / (12995 * 113.995613950713) + 0.122218809829 := by gcongr
    _ ≤ (0.159392147924 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052464718041)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347969664) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280930526398) :
    parallelOracle 12995 0.011 xi bn cd ≤ 0.160360121187 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12995 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12995 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516606217 : ℝ) ≤ plow 12995 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.995613950713 : ℝ) ≤ √(12995 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280930526398 : ℝ) / (2 * 0.560516606217 * 113.995613950713)) * 0.159392147924 +
        0.280930526398 ^ 2 / (2 * 0.560516606217 * 113.995613950713) := by gcongr
    _ ≤ (0.160360121187 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052464718041) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347969664)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280930526398) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12995 12995 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516606217 : ℝ) ≤ plow 12995 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.995613950713 : ℝ) ≤ √(12995 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12995 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12995 Θ 1.22 ≤ 0.011632908093 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.995613950713 := by gcongr <;> linarith
      _ ≤ (0.011632908093 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12995 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12995 12995 0.011 ≤ 0.008385295825 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12995 12995 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12995 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12995 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12995 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12995 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160360121187 + 0.011632908093 + (0.008385295825 : ℝ) *
        (1 + 2 * (0.280930526398 + 0.011632908093) / (0.560516606217 * 113.995613950713))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12995]

end BstLean.Part269.N12995

/-! The original eight local profiles supply actual 12995 moment certificates. -/
namespace BstLean.Part269.N12995
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12995 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12995 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12995 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052464718041 ∧
    0 ≤ bN 12995 BstLean.Part154.csC (groupTheta g) ∧ bN 12995 BstLean.Part154.csC (groupTheta g) ≤ 0.001347969664 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12995 12995 0.011
      (momentAllowance 12995 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12995 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12995 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12995 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12995 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12995 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229051780262 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12995 0.011
      (momentAllowance 12995 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12995 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12995
/-! The actual computed-centre upper energy formula at 12995. -/
namespace BstLean.Part269.N12995
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12995

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12995
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12995)
open BstLean.Part268 (cell12995)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084673218028
  | 2 => 0.085602064518
  | 3 => 0.086527146423
  | 4 => 0.087449434264
  | 5 => 0.088370115111
  | 6 => 0.089290626388
  | 7 => 0.090212693160
  | 8 => 0.091138369019
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12995 12995 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12995 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12995

/-! Actual upper energy certificates on all 43 source endpoints at 12995. -/
namespace BstLean.Part269.N12995
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12995)
open BstLean.Part268 (cell12995)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12995 (gMinus 12995) (1 - (cell12995 i).lower) ≤ 1 ∧
    energyUpper 12995 (gMinus 12995) (BstLean.Part211.gPlus 12995)
      (finiteEnergy 12995 12995 0.011) (1 - (cell12995 i).lower) ≤
      (cell12995 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨10,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨11,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨12,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨13,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨14,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨15,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨16,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨17,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨18,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨19,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨20,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨21,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨22,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨23,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨24,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨25,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨26,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨27,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨28,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨29,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨30,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨31,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨32,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨33,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨34,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨35,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨36,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨37,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨38,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨39,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨40,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨41,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨42,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨43,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨44,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨45,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨46,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨47,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨48,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨49,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨50,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨51,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12995) (by norm_num)
        (q := 1 - (cell12995 ⟨52,by decide⟩).lower)
        (by norm_num [cell12995]) (by norm_num [cell12995])
      exact ⟨E.1,E.2.trans (by norm_num [cell12995])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12995

/-! Source-cell containment and simple scalar guards at 12995. -/
namespace BstLean.Part269.N12995
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12995)
open BstLean.Part268 (cell12995)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12995 ⟨10,by decide⟩).lower ∧ (cell12995 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12995 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12995 ⟨11,by decide⟩).lower ∧ (cell12995 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12995 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12995 ⟨12,by decide⟩).lower ∧ (cell12995 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12995 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12995 ⟨13,by decide⟩).lower ∧ (cell12995 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12995 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12995 ⟨14,by decide⟩).lower ∧ (cell12995 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12995 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12995 ⟨15,by decide⟩).lower ∧ (cell12995 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12995 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12995 ⟨16,by decide⟩).lower ∧ (cell12995 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12995 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12995 ⟨17,by decide⟩).lower ∧ (cell12995 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12995 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12995 ⟨18,by decide⟩).lower ∧ (cell12995 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12995 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12995 ⟨19,by decide⟩).lower ∧ (cell12995 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12995 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12995 ⟨20,by decide⟩).lower ∧ (cell12995 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12995 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12995 ⟨21,by decide⟩).lower ∧ (cell12995 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12995 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12995 ⟨22,by decide⟩).lower ∧ (cell12995 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12995 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12995 ⟨23,by decide⟩).lower ∧ (cell12995 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12995 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12995 ⟨24,by decide⟩).lower ∧ (cell12995 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12995 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12995 ⟨25,by decide⟩).lower ∧ (cell12995 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12995 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12995 ⟨26,by decide⟩).lower ∧ (cell12995 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12995 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12995 ⟨27,by decide⟩).lower ∧ (cell12995 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12995 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12995 ⟨28,by decide⟩).lower ∧ (cell12995 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12995 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12995 ⟨29,by decide⟩).lower ∧ (cell12995 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12995 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12995 ⟨30,by decide⟩).lower ∧ (cell12995 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12995 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12995 ⟨31,by decide⟩).lower ∧ (cell12995 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12995 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12995 ⟨32,by decide⟩).lower ∧ (cell12995 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12995 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12995 ⟨33,by decide⟩).lower ∧ (cell12995 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12995 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12995 ⟨34,by decide⟩).lower ∧ (cell12995 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12995 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12995 ⟨35,by decide⟩).lower ∧ (cell12995 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12995 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12995 ⟨36,by decide⟩).lower ∧ (cell12995 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12995 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12995 ⟨37,by decide⟩).lower ∧ (cell12995 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12995 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12995 ⟨38,by decide⟩).lower ∧ (cell12995 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12995 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12995 ⟨39,by decide⟩).lower ∧ (cell12995 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12995 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12995 ⟨40,by decide⟩).lower ∧ (cell12995 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12995 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12995 ⟨41,by decide⟩).lower ∧ (cell12995 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12995 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12995 ⟨42,by decide⟩).lower ∧ (cell12995 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12995 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12995 ⟨43,by decide⟩).lower ∧ (cell12995 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12995 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12995 ⟨44,by decide⟩).lower ∧ (cell12995 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12995 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12995 ⟨45,by decide⟩).lower ∧ (cell12995 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12995 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12995 ⟨46,by decide⟩).lower ∧ (cell12995 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12995 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12995 ⟨47,by decide⟩).lower ∧ (cell12995 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12995 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12995 ⟨48,by decide⟩).lower ∧ (cell12995 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12995 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12995 ⟨49,by decide⟩).lower ∧ (cell12995 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12995 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12995 ⟨50,by decide⟩).lower ∧ (cell12995 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12995 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12995 ⟨51,by decide⟩).lower ∧ (cell12995 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12995 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12995 ⟨52,by decide⟩).lower ∧ (cell12995 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12995 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12995 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12995 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12995,cell12995,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12995 i).lower ∧
    (cell12995 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12995 i).upper ≤ (0.532 : ℝ) ∧
    (cell12995 i).centre ≤ (0.1 : ℝ) ∧ (cell12995 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12995 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12995 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12995

/-! The local source numeric instances at 12995 have no network premises. -/
namespace BstLean.Part269.N12995
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12995)
open BstLean.Part268 (cell12995)

noncomputable def sourceNumerics12995 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12995 (cell12995 i)
      scalarRow12995.M scalarRow12995.H scalarRow12995.xi := by
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
    energy_allowance := scalarRow12995.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12995]
    centre_nonneg := (scalarRow12995.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12995])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12995
/-! Actual 12996 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12996
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12996 ≤ (1.035395506310 : ℝ) := by
  have hr : (114.000000000000 : ℝ) ≤ √(12996 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.000000000000 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12996 12996 (11 / 1000) ≤
    (0.008384973205 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12996) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.000000000000 : ℝ) ≤ √(12996 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12996)
  have hdiv : K / √(12996 : ℝ) ≤ K / 114.000000000000 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.000000000000 ≤ (0.008384973205 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12996.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12996 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12996 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12996 := gPlus_lower 12996
end BstLean.Part269.N12996

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12996
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035395506309 : ℝ) ≤ wn 12996 := by
  have hn : √(12996 : ℝ) ≤ 114.000000000000 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12996 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.000000000000 ≤ 2 / √(12996 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246045657 : ℝ) ≤ rhoBar 12996 BstLean.Part154.csC ∧
    rhoBar 12996 BstLean.Part154.csC ≤ 0.000246046038 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035395506309 : ℝ) / (1.295212 * 12996) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035395506310 : ℝ) / (1.29521 * 12996) := by gcongr
      _ ≤ (0.000246046038 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12996 BstLean.Part154.csC) ≤ 0.000984244691 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12996 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12996 BstLean.Part154.csC) (piBar (rhoBar 12996 BstLean.Part154.csC)) ≤ 0.000187931421 ∧
    cc1 (rhoBar 12996 BstLean.Part154.csC) (piBar (rhoBar 12996 BstLean.Part154.csC)) ≤ 0.000119582053 ∧
    cc2 (rhoBar 12996 BstLean.Part154.csC) ≤ 0.000069418348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12996 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12996 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12996 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12996 BstLean.Part154.csC * nuR (rhoBar 12996 BstLean.Part154.csC)) ≤ 0.000492107211 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246046038 : ℝ) * 0.000984244691 := by gcongr
      _ ≤ (0.000492107211 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12996 BstLean.Part154.csC) * nuR (rhoBar 12996 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000984244691 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12996 BstLean.Part154.csC) * rhoBar 12996 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246046038 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246046038 / 2 + 0.399 * 0.000984244691 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187931421 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492107211 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119582053 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246046038 / 1.414213562 := by gcongr
      _ ≤ (0.000069418348 : ℝ) := by norm_num

end BstLean.Part269.N12996

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12996
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12996 BstLean.Part154.csC) (piBar (rhoBar 12996 BstLean.Part154.csC)) ≤ 1.52523E-7 := by
  have hr0 : 0 ≤ rhoBar 12996 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12996 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12996 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12996 BstLean.Part154.csC) (piBar (rhoBar 12996 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12996 BstLean.Part154.csC) (piBar (rhoBar 12996 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12996 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187931421 : ℝ) ^ 2 + 0.000119582053 ^ 2 + 3 * 0.000069418348 ^ 2 +
        2 * 0.797885 * 0.000187931421 * 0.000119582053 + 2 * 0.000187931421 * 0.000069418348 +
        4 * 0.797885 * 0.000119582053 * 0.000069418348 := by gcongr
    _ ≤ (1.52523E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12996 BstLean.Part154.csC Θ ≤ 0.002567354868 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12996 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12996 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12996 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12996 BstLean.Part154.csC) (piBar (rhoBar 12996 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12996 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035395506310 * 1.52523E-7 / (0.000246045657 : ℝ) := by gcongr
    _ ≤ 0.002567354868 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12996 BstLean.Part154.csC Θ ≤ 0.002847473188 + 0.000648728319 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12996 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12996 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12996 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035395506310 : ℝ) * ((2 * Θ * 0.000246046038 +
        (6863 / 10000) * 0.000246046038 * 12996 * 0.000984244691) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002847473188 + 0.000648728319 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12996 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12996 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12996 0.011 Θ ∧ gammaRatio 12996 0.011 Θ ≤ 0.000084584266 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12996 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035395506310 : ℝ) * 0.525 / ((1 - 0.011) * 12996) := by gcongr
      _ ≤ (0.000084584266 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12996 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12996 0.011 Θ) :=
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
    badAllowance 12996 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12996 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 12996 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12996 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12996 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12996 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 12996 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12996 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12996 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12996 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12996 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035395506310 : ℝ) * 12996 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12996 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003269308411 + 0.003216083187 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12996

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12996
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12996 BstLean.Part154.csC) (piBar (rhoBar 12996 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12996 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12996 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12996 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12996 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12996 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12996 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12996 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12996 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12996 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12996 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12996 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12996 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12996 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12996 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051876728746 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12996) ≤ 0.010475768255 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12996 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035395506310)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010475768255 + 2 * 0.737676 / 12996) := by gcongr
    _ ≤ (0.051876728746 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12996 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12996

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12996
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516649407 : ℝ) ≤ plow 12996 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12996) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052464352085)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347861306) : eMP 12996 0.011 xi bn ≤ 0.001160777752 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12996 : ℝ) * (1 - 0.011))) ≤ 0.000573977101 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001347861306 / (12996 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573977101 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573977101 : ℝ) + 3.141593 * 0.052464352085 / (12996 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001160777752 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052464352085)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347861306) : PiBarMP 12996 12 0.011 xi bn ≤ 0.159385945566 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12996 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036713230667 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.371266200920 : ℝ) ≤ √((12996 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.000000000000 : ℝ) ≤ √(12996 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12996) ≤ 0.122214107568 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036713230667 + 0.052464352085 * 1.772454 / (2 * (113.371266200920 : ℝ))) * (1 + 0.001160777752) +
        8 / (12996 * 114.000000000000) + 0.122214107568 := by gcongr
    _ ≤ (0.159385945566 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052464352085)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347861306) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280927710157) :
    parallelOracle 12996 0.011 xi bn cd ≤ 0.160353851985 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12996 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12996 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516649407 : ℝ) ≤ plow 12996 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.000000000000 : ℝ) ≤ √(12996 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280927710157 : ℝ) / (2 * 0.560516649407 * 114.000000000000)) * 0.159385945566 +
        0.280927710157 ^ 2 / (2 * 0.560516649407 * 114.000000000000) := by gcongr
    _ ≤ (0.160353851985 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052464352085) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347861306)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280927710157) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12996 12996 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516649407 : ℝ) ≤ plow 12996 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.000000000000 : ℝ) ≤ √(12996 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12996 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12996 Θ 1.22 ≤ 0.011632460527 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.000000000000 := by gcongr <;> linarith
      _ ≤ (0.011632460527 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12996 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12996 12996 0.011 ≤ 0.008384973205 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12996 12996 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12996 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12996 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12996 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12996 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160353851985 + 0.011632460527 + (0.008384973205 : ℝ) *
        (1 + 2 * (0.280927710157 + 0.011632460527) / (0.560516649407 * 114.000000000000))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12996]

end BstLean.Part269.N12996

/-! The original eight local profiles supply actual 12996 moment certificates. -/
namespace BstLean.Part269.N12996
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12996 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12996 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12996 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052464352085 ∧
    0 ≤ bN 12996 BstLean.Part154.csC (groupTheta g) ∧ bN 12996 BstLean.Part154.csC (groupTheta g) ≤ 0.001347861306 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12996 12996 0.011
      (momentAllowance 12996 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12996 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12996 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12996 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12996 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12996 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229050981411 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12996 0.011
      (momentAllowance 12996 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12996 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12996
/-! The actual computed-centre upper energy formula at 12996. -/
namespace BstLean.Part269.N12996
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12996

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12996
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12996)
open BstLean.Part268 (cell12996)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084670595772
  | 2 => 0.085599407571
  | 3 => 0.086524449495
  | 4 => 0.087446690826
  | 5 => 0.088367317173
  | 6 => 0.089287764239
  | 7 => 0.090209755086
  | 8 => 0.091135340980
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12996 12996 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12996 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12996

/-! Actual upper energy certificates on all 43 source endpoints at 12996. -/
namespace BstLean.Part269.N12996
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12996)
open BstLean.Part268 (cell12996)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12996 (gMinus 12996) (1 - (cell12996 i).lower) ≤ 1 ∧
    energyUpper 12996 (gMinus 12996) (BstLean.Part211.gPlus 12996)
      (finiteEnergy 12996 12996 0.011) (1 - (cell12996 i).lower) ≤
      (cell12996 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨10,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨11,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨12,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨13,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨14,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨15,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨16,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨17,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨18,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨19,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨20,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨21,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨22,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨23,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨24,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨25,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨26,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨27,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨28,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨29,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨30,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨31,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨32,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨33,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨34,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨35,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨36,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨37,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨38,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨39,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨40,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨41,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨42,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨43,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨44,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨45,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨46,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨47,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨48,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨49,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨50,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨51,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12996) (by norm_num)
        (q := 1 - (cell12996 ⟨52,by decide⟩).lower)
        (by norm_num [cell12996]) (by norm_num [cell12996])
      exact ⟨E.1,E.2.trans (by norm_num [cell12996])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12996

/-! Source-cell containment and simple scalar guards at 12996. -/
namespace BstLean.Part269.N12996
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12996)
open BstLean.Part268 (cell12996)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12996 ⟨10,by decide⟩).lower ∧ (cell12996 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12996 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12996 ⟨11,by decide⟩).lower ∧ (cell12996 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12996 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12996 ⟨12,by decide⟩).lower ∧ (cell12996 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12996 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12996 ⟨13,by decide⟩).lower ∧ (cell12996 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12996 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12996 ⟨14,by decide⟩).lower ∧ (cell12996 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12996 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12996 ⟨15,by decide⟩).lower ∧ (cell12996 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12996 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12996 ⟨16,by decide⟩).lower ∧ (cell12996 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12996 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12996 ⟨17,by decide⟩).lower ∧ (cell12996 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12996 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12996 ⟨18,by decide⟩).lower ∧ (cell12996 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12996 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12996 ⟨19,by decide⟩).lower ∧ (cell12996 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12996 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12996 ⟨20,by decide⟩).lower ∧ (cell12996 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12996 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12996 ⟨21,by decide⟩).lower ∧ (cell12996 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12996 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12996 ⟨22,by decide⟩).lower ∧ (cell12996 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12996 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12996 ⟨23,by decide⟩).lower ∧ (cell12996 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12996 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12996 ⟨24,by decide⟩).lower ∧ (cell12996 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12996 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12996 ⟨25,by decide⟩).lower ∧ (cell12996 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12996 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12996 ⟨26,by decide⟩).lower ∧ (cell12996 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12996 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12996 ⟨27,by decide⟩).lower ∧ (cell12996 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12996 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12996 ⟨28,by decide⟩).lower ∧ (cell12996 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12996 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12996 ⟨29,by decide⟩).lower ∧ (cell12996 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12996 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12996 ⟨30,by decide⟩).lower ∧ (cell12996 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12996 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12996 ⟨31,by decide⟩).lower ∧ (cell12996 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12996 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12996 ⟨32,by decide⟩).lower ∧ (cell12996 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12996 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12996 ⟨33,by decide⟩).lower ∧ (cell12996 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12996 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12996 ⟨34,by decide⟩).lower ∧ (cell12996 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12996 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12996 ⟨35,by decide⟩).lower ∧ (cell12996 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12996 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12996 ⟨36,by decide⟩).lower ∧ (cell12996 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12996 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12996 ⟨37,by decide⟩).lower ∧ (cell12996 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12996 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12996 ⟨38,by decide⟩).lower ∧ (cell12996 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12996 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12996 ⟨39,by decide⟩).lower ∧ (cell12996 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12996 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12996 ⟨40,by decide⟩).lower ∧ (cell12996 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12996 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12996 ⟨41,by decide⟩).lower ∧ (cell12996 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12996 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12996 ⟨42,by decide⟩).lower ∧ (cell12996 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12996 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12996 ⟨43,by decide⟩).lower ∧ (cell12996 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12996 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12996 ⟨44,by decide⟩).lower ∧ (cell12996 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12996 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12996 ⟨45,by decide⟩).lower ∧ (cell12996 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12996 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12996 ⟨46,by decide⟩).lower ∧ (cell12996 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12996 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12996 ⟨47,by decide⟩).lower ∧ (cell12996 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12996 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12996 ⟨48,by decide⟩).lower ∧ (cell12996 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12996 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12996 ⟨49,by decide⟩).lower ∧ (cell12996 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12996 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12996 ⟨50,by decide⟩).lower ∧ (cell12996 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12996 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12996 ⟨51,by decide⟩).lower ∧ (cell12996 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12996 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12996 ⟨52,by decide⟩).lower ∧ (cell12996 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12996 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12996 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12996 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12996,cell12996,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12996 i).lower ∧
    (cell12996 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12996 i).upper ≤ (0.532 : ℝ) ∧
    (cell12996 i).centre ≤ (0.1 : ℝ) ∧ (cell12996 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12996 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12996 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12996

/-! The local source numeric instances at 12996 have no network premises. -/
namespace BstLean.Part269.N12996
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12996)
open BstLean.Part268 (cell12996)

noncomputable def sourceNumerics12996 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12996 (cell12996 i)
      scalarRow12996.M scalarRow12996.H scalarRow12996.xi := by
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
    energy_allowance := scalarRow12996.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12996]
    centre_nonneg := (scalarRow12996.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12996])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12996
/-! Actual 12997 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12997
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12997 ≤ (1.035394132764 : ℝ) := by
  have hr : (114.004385880544 : ℝ) ≤ √(12997 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.004385880544 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12997 12997 (11 / 1000) ≤
    (0.008384650623 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12997) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.004385880544 : ℝ) ≤ √(12997 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12997)
  have hdiv : K / √(12997 : ℝ) ≤ K / 114.004385880544 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.004385880544 ≤ (0.008384650623 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12997.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12997 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12997 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12997 := gPlus_lower 12997
end BstLean.Part269.N12997

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12997
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035394132763 : ℝ) ≤ wn 12997 := by
  have hn : √(12997 : ℝ) ≤ 114.004385880545 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12997 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.004385880545 ≤ 2 / √(12997 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246026400 : ℝ) ≤ rhoBar 12997 BstLean.Part154.csC ∧
    rhoBar 12997 BstLean.Part154.csC ≤ 0.000246026781 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035394132763 : ℝ) / (1.295212 * 12997) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035394132764 : ℝ) / (1.29521 * 12997) := by gcongr
      _ ≤ (0.000246026781 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12997 BstLean.Part154.csC) ≤ 0.000984167654 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12997 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12997 BstLean.Part154.csC) (piBar (rhoBar 12997 BstLean.Part154.csC)) ≤ 0.000187916712 ∧
    cc1 (rhoBar 12997 BstLean.Part154.csC) (piBar (rhoBar 12997 BstLean.Part154.csC)) ≤ 0.000119572693 ∧
    cc2 (rhoBar 12997 BstLean.Part154.csC) ≤ 0.000069412915 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12997 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12997 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12997 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12997 BstLean.Part154.csC * nuR (rhoBar 12997 BstLean.Part154.csC)) ≤ 0.000492068695 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246026781 : ℝ) * 0.000984167654 := by gcongr
      _ ≤ (0.000492068695 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12997 BstLean.Part154.csC) * nuR (rhoBar 12997 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000984167654 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12997 BstLean.Part154.csC) * rhoBar 12997 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246026781 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246026781 / 2 + 0.399 * 0.000984167654 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187916712 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492068695 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119572693 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246026781 / 1.414213562 := by gcongr
      _ ≤ (0.000069412915 : ℝ) := by norm_num

end BstLean.Part269.N12997

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12997
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12997 BstLean.Part154.csC) (piBar (rhoBar 12997 BstLean.Part154.csC)) ≤ 1.52499E-7 := by
  have hr0 : 0 ≤ rhoBar 12997 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12997 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12997 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12997 BstLean.Part154.csC) (piBar (rhoBar 12997 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12997 BstLean.Part154.csC) (piBar (rhoBar 12997 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12997 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187916712 : ℝ) ^ 2 + 0.000119572693 ^ 2 + 3 * 0.000069412915 ^ 2 +
        2 * 0.797885 * 0.000187916712 * 0.000119572693 + 2 * 0.000187916712 * 0.000069412915 +
        4 * 0.797885 * 0.000119572693 * 0.000069412915 := by gcongr
    _ ≤ (1.52499E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12997 BstLean.Part154.csC Θ ≤ 0.002567148402 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12997 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12997 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12997 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12997 BstLean.Part154.csC) (piBar (rhoBar 12997 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12997 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035394132764 * 1.52499E-7 / (0.000246026400 : ℝ) := by gcongr
    _ ≤ 0.002567148402 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12997 BstLean.Part154.csC Θ ≤ 0.002847242766 + 0.000648676686 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12997 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12997 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12997 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035394132764 : ℝ) * ((2 * Θ * 0.000246026781 +
        (6863 / 10000) * 0.000246026781 * 12997 * 0.000984167654) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002847242766 + 0.000648676686 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12997 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12997 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12997 0.011 Θ ∧ gammaRatio 12997 0.011 Θ ≤ 0.000084577645 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12997 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035394132764 : ℝ) * 0.525 / ((1 - 0.011) * 12997) := by gcongr
      _ ≤ (0.000084577645 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12997 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12997 0.011 Θ) :=
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
    badAllowance 12997 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12997 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 12997 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12997 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12997 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12997 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 12997 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12997 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12997 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12997 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12997 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035394132764 : ℝ) * 12997 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12997 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003269077989 + 0.003215825088 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12997

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12997
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12997 BstLean.Part154.csC) (piBar (rhoBar 12997 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12997 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12997 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12997 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12997 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12997 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12997 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12997 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12997 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12997 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12997 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12997 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12997 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12997 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12997 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051874711593 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12997) ≤ 0.010475365240 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12997 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035394132764)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010475365240 + 2 * 0.737676 / 12997) := by gcongr
    _ ≤ (0.051874711593 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12997 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12997

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12997
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516692590 : ℝ) ≤ plow 12997 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12997) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052463986161)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347752912) : eMP 12997 0.011 xi bn ≤ 0.001160686356 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12997 : ℝ) * (1 - 0.011))) ≤ 0.000573931941 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001347752912 / (12997 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573931941 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573931941 : ℝ) + 3.141593 * 0.052463986161 / (12997 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001160686356 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052463986161)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347752912) : PiBarMP 12997 12 0.011 xi bn ≤ 0.159379743204 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12997 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036711754412 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.375627892417 : ℝ) ≤ √((12997 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.004385880544 : ℝ) ≤ √(12997 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12997) ≤ 0.122209405850 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036711754412 + 0.052463986161 * 1.772454 / (2 * (113.375627892417 : ℝ))) * (1 + 0.001160686356) +
        8 / (12997 * 114.004385880544) + 0.122209405850 := by gcongr
    _ ≤ (0.159379743204 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052463986161)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347752912) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280924894219) :
    parallelOracle 12997 0.011 xi bn cd ≤ 0.160347582787 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12997 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12997 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516692590 : ℝ) ≤ plow 12997 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.004385880544 : ℝ) ≤ √(12997 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280924894219 : ℝ) / (2 * 0.560516692590 * 114.004385880544)) * 0.159379743204 +
        0.280924894219 ^ 2 / (2 * 0.560516692590 * 114.004385880544) := by gcongr
    _ ≤ (0.160347582787 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052463986161) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347752912)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280924894219) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12997 12997 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516692590 : ℝ) ≤ plow 12997 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.004385880544 : ℝ) ≤ √(12997 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12997 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12997 Θ 1.22 ≤ 0.011632013013 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.004385880544 := by gcongr <;> linarith
      _ ≤ (0.011632013013 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12997 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12997 12997 0.011 ≤ 0.008384650623 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12997 12997 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12997 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12997 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12997 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12997 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160347582787 + 0.011632013013 + (0.008384650623 : ℝ) *
        (1 + 2 * (0.280924894219 + 0.011632013013) / (0.560516692590 * 114.004385880544))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12997]

end BstLean.Part269.N12997

/-! The original eight local profiles supply actual 12997 moment certificates. -/
namespace BstLean.Part269.N12997
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12997 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12997 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12997 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052463986161 ∧
    0 ≤ bN 12997 BstLean.Part154.csC (groupTheta g) ∧ bN 12997 BstLean.Part154.csC (groupTheta g) ≤ 0.001347752912 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12997 12997 0.011
      (momentAllowance 12997 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12997 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12997 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12997 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12997 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12997 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229050182626 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12997 0.011
      (momentAllowance 12997 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12997 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12997
/-! The actual computed-centre upper energy formula at 12997. -/
namespace BstLean.Part269.N12997
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12997

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12997
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12997)
open BstLean.Part268 (cell12997)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084667974326
  | 2 => 0.085596751464
  | 3 => 0.086521753441
  | 4 => 0.087443948307
  | 5 => 0.088364520206
  | 6 => 0.089284903128
  | 7 => 0.090206818130
  | 8 => 0.091132314156
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12997 12997 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12997 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12997

/-! Actual upper energy certificates on all 43 source endpoints at 12997. -/
namespace BstLean.Part269.N12997
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12997)
open BstLean.Part268 (cell12997)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12997 (gMinus 12997) (1 - (cell12997 i).lower) ≤ 1 ∧
    energyUpper 12997 (gMinus 12997) (BstLean.Part211.gPlus 12997)
      (finiteEnergy 12997 12997 0.011) (1 - (cell12997 i).lower) ≤
      (cell12997 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨10,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨11,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨12,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨13,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨14,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨15,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨16,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨17,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨18,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨19,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨20,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨21,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨22,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨23,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨24,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨25,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨26,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨27,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨28,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨29,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨30,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨31,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨32,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨33,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨34,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨35,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨36,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨37,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨38,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨39,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨40,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨41,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨42,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨43,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨44,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨45,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨46,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨47,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨48,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨49,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨50,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨51,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12997) (by norm_num)
        (q := 1 - (cell12997 ⟨52,by decide⟩).lower)
        (by norm_num [cell12997]) (by norm_num [cell12997])
      exact ⟨E.1,E.2.trans (by norm_num [cell12997])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12997

/-! Source-cell containment and simple scalar guards at 12997. -/
namespace BstLean.Part269.N12997
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12997)
open BstLean.Part268 (cell12997)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12997 ⟨10,by decide⟩).lower ∧ (cell12997 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12997 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12997 ⟨11,by decide⟩).lower ∧ (cell12997 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12997 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12997 ⟨12,by decide⟩).lower ∧ (cell12997 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12997 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12997 ⟨13,by decide⟩).lower ∧ (cell12997 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12997 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12997 ⟨14,by decide⟩).lower ∧ (cell12997 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12997 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12997 ⟨15,by decide⟩).lower ∧ (cell12997 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12997 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12997 ⟨16,by decide⟩).lower ∧ (cell12997 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12997 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12997 ⟨17,by decide⟩).lower ∧ (cell12997 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12997 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12997 ⟨18,by decide⟩).lower ∧ (cell12997 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12997 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12997 ⟨19,by decide⟩).lower ∧ (cell12997 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12997 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12997 ⟨20,by decide⟩).lower ∧ (cell12997 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12997 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12997 ⟨21,by decide⟩).lower ∧ (cell12997 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12997 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12997 ⟨22,by decide⟩).lower ∧ (cell12997 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12997 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12997 ⟨23,by decide⟩).lower ∧ (cell12997 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12997 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12997 ⟨24,by decide⟩).lower ∧ (cell12997 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12997 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12997 ⟨25,by decide⟩).lower ∧ (cell12997 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12997 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12997 ⟨26,by decide⟩).lower ∧ (cell12997 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12997 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12997 ⟨27,by decide⟩).lower ∧ (cell12997 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12997 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12997 ⟨28,by decide⟩).lower ∧ (cell12997 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12997 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12997 ⟨29,by decide⟩).lower ∧ (cell12997 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12997 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12997 ⟨30,by decide⟩).lower ∧ (cell12997 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12997 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12997 ⟨31,by decide⟩).lower ∧ (cell12997 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12997 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12997 ⟨32,by decide⟩).lower ∧ (cell12997 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12997 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12997 ⟨33,by decide⟩).lower ∧ (cell12997 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12997 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12997 ⟨34,by decide⟩).lower ∧ (cell12997 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12997 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12997 ⟨35,by decide⟩).lower ∧ (cell12997 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12997 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12997 ⟨36,by decide⟩).lower ∧ (cell12997 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12997 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12997 ⟨37,by decide⟩).lower ∧ (cell12997 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12997 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12997 ⟨38,by decide⟩).lower ∧ (cell12997 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12997 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12997 ⟨39,by decide⟩).lower ∧ (cell12997 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12997 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12997 ⟨40,by decide⟩).lower ∧ (cell12997 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12997 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12997 ⟨41,by decide⟩).lower ∧ (cell12997 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12997 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12997 ⟨42,by decide⟩).lower ∧ (cell12997 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12997 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12997 ⟨43,by decide⟩).lower ∧ (cell12997 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12997 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12997 ⟨44,by decide⟩).lower ∧ (cell12997 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12997 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12997 ⟨45,by decide⟩).lower ∧ (cell12997 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12997 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12997 ⟨46,by decide⟩).lower ∧ (cell12997 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12997 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12997 ⟨47,by decide⟩).lower ∧ (cell12997 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12997 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12997 ⟨48,by decide⟩).lower ∧ (cell12997 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12997 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12997 ⟨49,by decide⟩).lower ∧ (cell12997 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12997 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12997 ⟨50,by decide⟩).lower ∧ (cell12997 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12997 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12997 ⟨51,by decide⟩).lower ∧ (cell12997 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12997 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12997 ⟨52,by decide⟩).lower ∧ (cell12997 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12997 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12997 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12997 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12997,cell12997,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12997 i).lower ∧
    (cell12997 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12997 i).upper ≤ (0.532 : ℝ) ∧
    (cell12997 i).centre ≤ (0.1 : ℝ) ∧ (cell12997 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12997 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12997 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12997

/-! The local source numeric instances at 12997 have no network premises. -/
namespace BstLean.Part269.N12997
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12997)
open BstLean.Part268 (cell12997)

noncomputable def sourceNumerics12997 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12997 (cell12997 i)
      scalarRow12997.M scalarRow12997.H scalarRow12997.xi := by
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
    energy_allowance := scalarRow12997.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12997]
    centre_nonneg := (scalarRow12997.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12997])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12997
/-! Actual 12998 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12998
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12998 ≤ (1.035392759377 : ℝ) := by
  have hr : (114.008771592364 : ℝ) ≤ √(12998 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.008771592364 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12998 12998 (11 / 1000) ≤
    (0.008384328079 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12998) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.008771592364 : ℝ) ≤ √(12998 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12998)
  have hdiv : K / √(12998 : ℝ) ≤ K / 114.008771592364 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.008771592364 ≤ (0.008384328079 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12998.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12998 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12998 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12998 := gPlus_lower 12998
end BstLean.Part269.N12998

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12998
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035392759376 : ℝ) ≤ wn 12998 := by
  have hn : √(12998 : ℝ) ≤ 114.008771592365 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12998 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.008771592365 ≤ 2 / √(12998 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246007146 : ℝ) ≤ rhoBar 12998 BstLean.Part154.csC ∧
    rhoBar 12998 BstLean.Part154.csC ≤ 0.000246007526 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035392759376 : ℝ) / (1.295212 * 12998) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035392759377 : ℝ) / (1.29521 * 12998) := by gcongr
      _ ≤ (0.000246007526 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12998 BstLean.Part154.csC) ≤ 0.000984090624 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12998 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12998 BstLean.Part154.csC) (piBar (rhoBar 12998 BstLean.Part154.csC)) ≤ 0.000187902004 ∧
    cc1 (rhoBar 12998 BstLean.Part154.csC) (piBar (rhoBar 12998 BstLean.Part154.csC)) ≤ 0.000119563335 ∧
    cc2 (rhoBar 12998 BstLean.Part154.csC) ≤ 0.000069407483 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12998 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12998 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12998 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12998 BstLean.Part154.csC * nuR (rhoBar 12998 BstLean.Part154.csC)) ≤ 0.000492030182 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246007526 : ℝ) * 0.000984090624 := by gcongr
      _ ≤ (0.000492030182 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12998 BstLean.Part154.csC) * nuR (rhoBar 12998 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000984090624 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12998 BstLean.Part154.csC) * rhoBar 12998 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246007526 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246007526 / 2 + 0.399 * 0.000984090624 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187902004 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492030182 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119563335 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246007526 / 1.414213562 := by gcongr
      _ ≤ (0.000069407483 : ℝ) := by norm_num

end BstLean.Part269.N12998

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12998
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12998 BstLean.Part154.csC) (piBar (rhoBar 12998 BstLean.Part154.csC)) ≤ 1.52475E-7 := by
  have hr0 : 0 ≤ rhoBar 12998 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12998 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12998 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12998 BstLean.Part154.csC) (piBar (rhoBar 12998 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12998 BstLean.Part154.csC) (piBar (rhoBar 12998 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12998 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187902004 : ℝ) ^ 2 + 0.000119563335 ^ 2 + 3 * 0.000069407483 ^ 2 +
        2 * 0.797885 * 0.000187902004 * 0.000119563335 + 2 * 0.000187902004 * 0.000069407483 +
        4 * 0.797885 * 0.000119563335 * 0.000069407483 := by gcongr
    _ ≤ (1.52475E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12998 BstLean.Part154.csC Θ ≤ 0.002566941873 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12998 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12998 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12998 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12998 BstLean.Part154.csC) (piBar (rhoBar 12998 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12998 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035392759377 * 1.52475E-7 / (0.000246007146 : ℝ) := by gcongr
    _ ≤ 0.002566941873 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12998 BstLean.Part154.csC Θ ≤ 0.002847012354 + 0.000648625057 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12998 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12998 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12998 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035392759377 : ℝ) * ((2 * Θ * 0.000246007526 +
        (6863 / 10000) * 0.000246007526 * 12998 * 0.000984090624) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002847012354 + 0.000648625057 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12998 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12998 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12998 0.011 Θ ∧ gammaRatio 12998 0.011 Θ ≤ 0.000084571026 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12998 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035392759377 : ℝ) * 0.525 / ((1 - 0.011) * 12998) := by gcongr
      _ ≤ (0.000084571026 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12998 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12998 0.011 Θ) :=
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
    badAllowance 12998 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12998 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 12998 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12998 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12998 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12998 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 12998 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12998 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12998 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12998 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12998 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035392759377 : ℝ) * 12998 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12998 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003268847577 + 0.003215566930 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12998

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12998
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12998 BstLean.Part154.csC) (piBar (rhoBar 12998 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12998 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12998 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12998 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12998 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12998 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12998 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12998 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12998 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12998 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12998 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12998 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12998 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12998 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12998 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051872694677 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12998) ≤ 0.010474962272 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12998 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035392759377)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010474962272 + 2 * 0.737676 / 12998) := by gcongr
    _ ≤ (0.051872694677 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12998 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12998

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12998
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516735767 : ℝ) ≤ plow 12998 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12998) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052463620216)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347644484) : eMP 12998 0.011 xi bn ≤ 0.001160594950 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12998 : ℝ) * (1 - 0.011))) ≤ 0.000573886776 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001347644484 / (12998 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573886776 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573886776 : ℝ) + 3.141593 * 0.052463620216 / (12998 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001160594950 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052463620216)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347644484) : PiBarMP 12998 12 0.011 xi bn ≤ 0.159373540864 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12998 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036710277635 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.379989416122 : ℝ) ≤ √((12998 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.008771592364 : ℝ) ≤ √(12998 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12998) ≤ 0.122204704675 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036710277635 + 0.052463620216 * 1.772454 / (2 * (113.379989416122 : ℝ))) * (1 + 0.001160594950) +
        8 / (12998 * 114.008771592364) + 0.122204704675 := by gcongr
    _ ≤ (0.159373540864 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052463620216)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347644484) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280922078471) :
    parallelOracle 12998 0.011 xi bn cd ≤ 0.160341313619 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12998 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12998 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516735767 : ℝ) ≤ plow 12998 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.008771592364 : ℝ) ≤ √(12998 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280922078471 : ℝ) / (2 * 0.560516735767 * 114.008771592364)) * 0.159373540864 +
        0.280922078471 ^ 2 / (2 * 0.560516735767 * 114.008771592364) := by gcongr
    _ ≤ (0.160341313619 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052463620216) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347644484)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280922078471) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12998 12998 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516735767 : ℝ) ≤ plow 12998 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.008771592364 : ℝ) ≤ √(12998 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12998 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12998 Θ 1.22 ≤ 0.011631565550 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.008771592364 := by gcongr <;> linarith
      _ ≤ (0.011631565550 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12998 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12998 12998 0.011 ≤ 0.008384328079 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12998 12998 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12998 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12998 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12998 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12998 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160341313619 + 0.011631565550 + (0.008384328079 : ℝ) *
        (1 + 2 * (0.280922078471 + 0.011631565550) / (0.560516735767 * 114.008771592364))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12998]

end BstLean.Part269.N12998

/-! The original eight local profiles supply actual 12998 moment certificates. -/
namespace BstLean.Part269.N12998
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12998 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12998 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12998 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052463620216 ∧
    0 ≤ bN 12998 BstLean.Part154.csC (groupTheta g) ∧ bN 12998 BstLean.Part154.csC (groupTheta g) ≤ 0.001347644484 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12998 12998 0.011
      (momentAllowance 12998 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12998 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12998 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12998 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12998 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12998 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229049383794 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12998 0.011
      (momentAllowance 12998 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12998 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12998
/-! The actual computed-centre upper energy formula at 12998. -/
namespace BstLean.Part269.N12998
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12998

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12998
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12998)
open BstLean.Part268 (cell12998)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084665353690
  | 2 => 0.085594096194
  | 3 => 0.086519058262
  | 4 => 0.087441206706
  | 5 => 0.088361724212
  | 6 => 0.089282043054
  | 7 => 0.090203882291
  | 8 => 0.091129288546
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12998 12998 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12998 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12998

/-! Actual upper energy certificates on all 43 source endpoints at 12998. -/
namespace BstLean.Part269.N12998
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12998)
open BstLean.Part268 (cell12998)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12998 (gMinus 12998) (1 - (cell12998 i).lower) ≤ 1 ∧
    energyUpper 12998 (gMinus 12998) (BstLean.Part211.gPlus 12998)
      (finiteEnergy 12998 12998 0.011) (1 - (cell12998 i).lower) ≤
      (cell12998 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨10,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨11,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨12,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨13,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨14,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨15,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨16,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨17,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨18,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨19,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨20,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨21,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨22,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨23,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨24,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨25,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨26,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨27,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨28,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨29,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨30,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨31,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨32,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨33,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨34,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨35,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨36,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨37,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨38,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨39,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨40,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨41,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨42,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨43,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨44,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨45,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨46,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨47,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨48,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨49,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨50,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨51,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12998) (by norm_num)
        (q := 1 - (cell12998 ⟨52,by decide⟩).lower)
        (by norm_num [cell12998]) (by norm_num [cell12998])
      exact ⟨E.1,E.2.trans (by norm_num [cell12998])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12998

/-! Source-cell containment and simple scalar guards at 12998. -/
namespace BstLean.Part269.N12998
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12998)
open BstLean.Part268 (cell12998)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12998 ⟨10,by decide⟩).lower ∧ (cell12998 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12998 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12998 ⟨11,by decide⟩).lower ∧ (cell12998 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12998 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12998 ⟨12,by decide⟩).lower ∧ (cell12998 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12998 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12998 ⟨13,by decide⟩).lower ∧ (cell12998 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12998 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12998 ⟨14,by decide⟩).lower ∧ (cell12998 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12998 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12998 ⟨15,by decide⟩).lower ∧ (cell12998 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12998 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12998 ⟨16,by decide⟩).lower ∧ (cell12998 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12998 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12998 ⟨17,by decide⟩).lower ∧ (cell12998 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12998 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12998 ⟨18,by decide⟩).lower ∧ (cell12998 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12998 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12998 ⟨19,by decide⟩).lower ∧ (cell12998 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12998 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12998 ⟨20,by decide⟩).lower ∧ (cell12998 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12998 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12998 ⟨21,by decide⟩).lower ∧ (cell12998 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12998 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12998 ⟨22,by decide⟩).lower ∧ (cell12998 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12998 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12998 ⟨23,by decide⟩).lower ∧ (cell12998 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12998 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12998 ⟨24,by decide⟩).lower ∧ (cell12998 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12998 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12998 ⟨25,by decide⟩).lower ∧ (cell12998 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12998 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12998 ⟨26,by decide⟩).lower ∧ (cell12998 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12998 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12998 ⟨27,by decide⟩).lower ∧ (cell12998 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12998 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12998 ⟨28,by decide⟩).lower ∧ (cell12998 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12998 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12998 ⟨29,by decide⟩).lower ∧ (cell12998 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12998 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12998 ⟨30,by decide⟩).lower ∧ (cell12998 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12998 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12998 ⟨31,by decide⟩).lower ∧ (cell12998 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12998 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12998 ⟨32,by decide⟩).lower ∧ (cell12998 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12998 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12998 ⟨33,by decide⟩).lower ∧ (cell12998 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12998 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12998 ⟨34,by decide⟩).lower ∧ (cell12998 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12998 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12998 ⟨35,by decide⟩).lower ∧ (cell12998 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12998 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12998 ⟨36,by decide⟩).lower ∧ (cell12998 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12998 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12998 ⟨37,by decide⟩).lower ∧ (cell12998 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12998 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12998 ⟨38,by decide⟩).lower ∧ (cell12998 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12998 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12998 ⟨39,by decide⟩).lower ∧ (cell12998 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12998 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12998 ⟨40,by decide⟩).lower ∧ (cell12998 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12998 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12998 ⟨41,by decide⟩).lower ∧ (cell12998 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12998 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12998 ⟨42,by decide⟩).lower ∧ (cell12998 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12998 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12998 ⟨43,by decide⟩).lower ∧ (cell12998 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12998 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12998 ⟨44,by decide⟩).lower ∧ (cell12998 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12998 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12998 ⟨45,by decide⟩).lower ∧ (cell12998 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12998 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12998 ⟨46,by decide⟩).lower ∧ (cell12998 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12998 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12998 ⟨47,by decide⟩).lower ∧ (cell12998 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12998 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12998 ⟨48,by decide⟩).lower ∧ (cell12998 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12998 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12998 ⟨49,by decide⟩).lower ∧ (cell12998 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12998 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12998 ⟨50,by decide⟩).lower ∧ (cell12998 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12998 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12998 ⟨51,by decide⟩).lower ∧ (cell12998 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12998 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12998 ⟨52,by decide⟩).lower ∧ (cell12998 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12998 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12998 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12998 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12998,cell12998,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12998 i).lower ∧
    (cell12998 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12998 i).upper ≤ (0.532 : ℝ) ∧
    (cell12998 i).centre ≤ (0.1 : ℝ) ∧ (cell12998 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12998 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12998 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12998

/-! The local source numeric instances at 12998 have no network premises. -/
namespace BstLean.Part269.N12998
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12998)
open BstLean.Part268 (cell12998)

noncomputable def sourceNumerics12998 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12998 (cell12998 i)
      scalarRow12998.M scalarRow12998.H scalarRow12998.xi := by
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
    energy_allowance := scalarRow12998.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12998]
    centre_nonneg := (scalarRow12998.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12998])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12998
/-! Actual 12999 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12999
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12999 ≤ (1.035391386149 : ℝ) := by
  have hr : (114.013157135481 : ℝ) ≤ √(12999 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.013157135481 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12999 12999 (11 / 1000) ≤
    (0.008384005571 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12999) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.013157135481 : ℝ) ≤ √(12999 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12999)
  have hdiv : K / √(12999 : ℝ) ≤ K / 114.013157135481 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.013157135481 ≤ (0.008384005571 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12999.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12999 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12999 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12999 := gPlus_lower 12999
end BstLean.Part269.N12999

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12999
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035391386148 : ℝ) ≤ wn 12999 := by
  have hn : √(12999 : ℝ) ≤ 114.013157135482 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12999 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.013157135482 ≤ 2 / √(12999 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245987894 : ℝ) ≤ rhoBar 12999 BstLean.Part154.csC ∧
    rhoBar 12999 BstLean.Part154.csC ≤ 0.000245988275 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035391386148 : ℝ) / (1.295212 * 12999) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035391386149 : ℝ) / (1.29521 * 12999) := by gcongr
      _ ≤ (0.000245988275 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12999 BstLean.Part154.csC) ≤ 0.000984013611 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12999 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12999 BstLean.Part154.csC) (piBar (rhoBar 12999 BstLean.Part154.csC)) ≤ 0.000187887299 ∧
    cc1 (rhoBar 12999 BstLean.Part154.csC) (piBar (rhoBar 12999 BstLean.Part154.csC)) ≤ 0.000119553978 ∧
    cc2 (rhoBar 12999 BstLean.Part154.csC) ≤ 0.000069402051 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12999 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12999 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12999 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12999 BstLean.Part154.csC * nuR (rhoBar 12999 BstLean.Part154.csC)) ≤ 0.000491991678 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245988275 : ℝ) * 0.000984013611 := by gcongr
      _ ≤ (0.000491991678 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12999 BstLean.Part154.csC) * nuR (rhoBar 12999 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000984013611 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12999 BstLean.Part154.csC) * rhoBar 12999 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245988275 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245988275 / 2 + 0.399 * 0.000984013611 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187887299 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491991678 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119553978 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245988275 / 1.414213562 := by gcongr
      _ ≤ (0.000069402051 : ℝ) := by norm_num

end BstLean.Part269.N12999

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12999
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12999 BstLean.Part154.csC) (piBar (rhoBar 12999 BstLean.Part154.csC)) ≤ 1.52451E-7 := by
  have hr0 : 0 ≤ rhoBar 12999 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12999 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12999 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12999 BstLean.Part154.csC) (piBar (rhoBar 12999 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12999 BstLean.Part154.csC) (piBar (rhoBar 12999 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12999 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187887299 : ℝ) ^ 2 + 0.000119553978 ^ 2 + 3 * 0.000069402051 ^ 2 +
        2 * 0.797885 * 0.000187887299 * 0.000119553978 + 2 * 0.000187887299 * 0.000069402051 +
        4 * 0.797885 * 0.000119553978 * 0.000069402051 := by gcongr
    _ ≤ (1.52451E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12999 BstLean.Part154.csC Θ ≤ 0.002566735292 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12999 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12999 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12999 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12999 BstLean.Part154.csC) (piBar (rhoBar 12999 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12999 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035391386149 * 1.52451E-7 / (0.000245987894 : ℝ) := by gcongr
    _ ≤ 0.002566735292 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12999 BstLean.Part154.csC Θ ≤ 0.002846782005 + 0.000648573440 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12999 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12999 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12999 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035391386149 : ℝ) * ((2 * Θ * 0.000245988275 +
        (6863 / 10000) * 0.000245988275 * 12999 * 0.000984013611) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002846782005 + 0.000648573440 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12999 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12999 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12999 0.011 Θ ∧ gammaRatio 12999 0.011 Θ ≤ 0.000084564408 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12999 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035391386149 : ℝ) * 0.525 / ((1 - 0.011) * 12999) := by gcongr
      _ ≤ (0.000084564408 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12999 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12999 0.011 Θ) :=
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
    badAllowance 12999 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421835223 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12999 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 12999 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12999 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12999 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12999 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 12999 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12999 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12999 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12999 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12999 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035391386149 : ℝ) * 12999 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421835223 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12999 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003268617228 + 0.003215308732 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12999

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12999
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12999 BstLean.Part154.csC) (piBar (rhoBar 12999 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12999 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12999 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12999 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12999 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12999 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12999 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12999 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12999 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12999 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12999 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12999 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12999 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12999 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12999 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051870677993 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12999) ≤ 0.010474559350 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12999 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035391386149)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010474559350 + 2 * 0.737676 / 12999) := by gcongr
    _ ≤ (0.051870677993 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12999 12 ≤ 0.0015 := by
  exact BstLean.Part269.S25.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12999

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12999
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516778936 : ℝ) ≤ plow 12999 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12999) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052463254313)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347536029) : eMP 12999 0.011 xi bn ≤ 0.001160503540 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12999 : ℝ) * (1 - 0.011))) ≤ 0.000573841609 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001347536029 / (12999 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573841609 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573841609 : ℝ) + 3.141593 * 0.052463254313 / (12999 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001160503540 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052463254313)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347536029) : PiBarMP 12999 12 0.011 xi bn ≤ 0.159367338641 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12999 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036708800430 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.384350772053 : ℝ) ≤ √((12999 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.013157135481 : ℝ) ≤ √(12999 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12999) ≤ 0.122200004042 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036708800430 + 0.052463254313 * 1.772454 / (2 * (113.384350772053 : ℝ))) * (1 + 0.001160503540) +
        8 / (12999 * 114.013157135481) + 0.122200004042 := by gcongr
    _ ≤ (0.159367338641 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052463254313)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347536029) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280919263043) :
    parallelOracle 12999 0.011 xi bn cd ≤ 0.160335044577 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12999 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12999 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516778936 : ℝ) ≤ plow 12999 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.013157135481 : ℝ) ≤ √(12999 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280919263043 : ℝ) / (2 * 0.560516778936 * 114.013157135481)) * 0.159367338641 +
        0.280919263043 ^ 2 / (2 * 0.560516778936 * 114.013157135481) := by gcongr
    _ ≤ (0.160335044577 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052463254313) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347536029)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280919263043) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12999 12999 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516778936 : ℝ) ≤ plow 12999 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.013157135481 : ℝ) ≤ √(12999 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12999 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12999 Θ 1.22 ≤ 0.011631118139 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.013157135481 := by gcongr <;> linarith
      _ ≤ (0.011631118139 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12999 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12999 12999 0.011 ≤ 0.008384005571 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12999 12999 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12999 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12999 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12999 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12999 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160335044577 + 0.011631118139 + (0.008384005571 : ℝ) *
        (1 + 2 * (0.280919263043 + 0.011631118139) / (0.560516778936 * 114.013157135481))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12999]

end BstLean.Part269.N12999

/-! The original eight local profiles supply actual 12999 moment certificates. -/
namespace BstLean.Part269.N12999
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12999 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12999 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12999 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052463254313 ∧
    0 ≤ bN 12999 BstLean.Part154.csC (groupTheta g) ∧ bN 12999 BstLean.Part154.csC (groupTheta g) ≤ 0.001347536029 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12999 12999 0.011
      (momentAllowance 12999 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12999 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12999 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12999 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12999 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12999 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229048585050 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12999 0.011
      (momentAllowance 12999 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12999 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12999
/-! The actual computed-centre upper energy formula at 12999. -/
namespace BstLean.Part269.N12999
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12999

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12999
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12999)
open BstLean.Part268 (cell12999)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084662733863
  | 2 => 0.085591441763
  | 3 => 0.086516363956
  | 4 => 0.087438466021
  | 5 => 0.088358929188
  | 6 => 0.089279184017
  | 7 => 0.090200947568
  | 8 => 0.091126264148
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12999 12999 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12999 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003274156000 + 0.003221457154 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S25.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S25.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12999

/-! Actual upper energy certificates on all 43 source endpoints at 12999. -/
namespace BstLean.Part269.N12999
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12999)
open BstLean.Part268 (cell12999)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12999 (gMinus 12999) (1 - (cell12999 i).lower) ≤ 1 ∧
    energyUpper 12999 (gMinus 12999) (BstLean.Part211.gPlus 12999)
      (finiteEnergy 12999 12999 0.011) (1 - (cell12999 i).lower) ≤
      (cell12999 i).energy := by
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
      have E := BstLean.Part269.S25.uniformEnergy10 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨10,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy11 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨11,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy12 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨12,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy13 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨13,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy14 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨14,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy15 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨15,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy16 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨16,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy17 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨17,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy18 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨18,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy19 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨19,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy20 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨20,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy21 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨21,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy22 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨22,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy23 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨23,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy24 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨24,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy25 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨25,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy26 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨26,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy27 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨27,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy28 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨28,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy29 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨29,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy30 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨30,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy31 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨31,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy32 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨32,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy33 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨33,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy34 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨34,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy35 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨35,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy36 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨36,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy37 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨37,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy38 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨38,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy39 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨39,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy40 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨40,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy41 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨41,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy42 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨42,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy43 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨43,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy44 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨44,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy45 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨45,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy46 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨46,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy47 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨47,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy48 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨48,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy49 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨49,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy50 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨50,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy51 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨51,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S25.uniformEnergy52 (n := 12999) (by norm_num)
        (q := 1 - (cell12999 ⟨52,by decide⟩).lower)
        (by norm_num [cell12999]) (by norm_num [cell12999])
      exact ⟨E.1,E.2.trans (by norm_num [cell12999])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12999

/-! Source-cell containment and simple scalar guards at 12999. -/
namespace BstLean.Part269.N12999
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12999)
open BstLean.Part268 (cell12999)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12999 ⟨10,by decide⟩).lower ∧ (cell12999 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12999 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12999 ⟨11,by decide⟩).lower ∧ (cell12999 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12999 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12999 ⟨12,by decide⟩).lower ∧ (cell12999 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12999 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12999 ⟨13,by decide⟩).lower ∧ (cell12999 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12999 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12999 ⟨14,by decide⟩).lower ∧ (cell12999 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12999 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12999 ⟨15,by decide⟩).lower ∧ (cell12999 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12999 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12999 ⟨16,by decide⟩).lower ∧ (cell12999 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12999 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12999 ⟨17,by decide⟩).lower ∧ (cell12999 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12999 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12999 ⟨18,by decide⟩).lower ∧ (cell12999 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12999 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12999 ⟨19,by decide⟩).lower ∧ (cell12999 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12999 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12999 ⟨20,by decide⟩).lower ∧ (cell12999 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12999 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12999 ⟨21,by decide⟩).lower ∧ (cell12999 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12999 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12999 ⟨22,by decide⟩).lower ∧ (cell12999 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12999 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12999 ⟨23,by decide⟩).lower ∧ (cell12999 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12999 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12999 ⟨24,by decide⟩).lower ∧ (cell12999 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12999 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12999 ⟨25,by decide⟩).lower ∧ (cell12999 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12999 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12999 ⟨26,by decide⟩).lower ∧ (cell12999 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12999 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12999 ⟨27,by decide⟩).lower ∧ (cell12999 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12999 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12999 ⟨28,by decide⟩).lower ∧ (cell12999 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12999 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12999 ⟨29,by decide⟩).lower ∧ (cell12999 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12999 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12999 ⟨30,by decide⟩).lower ∧ (cell12999 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12999 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12999 ⟨31,by decide⟩).lower ∧ (cell12999 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12999 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12999 ⟨32,by decide⟩).lower ∧ (cell12999 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12999 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12999 ⟨33,by decide⟩).lower ∧ (cell12999 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12999 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12999 ⟨34,by decide⟩).lower ∧ (cell12999 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12999 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12999 ⟨35,by decide⟩).lower ∧ (cell12999 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12999 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12999 ⟨36,by decide⟩).lower ∧ (cell12999 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12999 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12999 ⟨37,by decide⟩).lower ∧ (cell12999 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12999 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12999 ⟨38,by decide⟩).lower ∧ (cell12999 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12999 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12999 ⟨39,by decide⟩).lower ∧ (cell12999 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12999 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12999 ⟨40,by decide⟩).lower ∧ (cell12999 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12999 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12999 ⟨41,by decide⟩).lower ∧ (cell12999 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12999 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12999 ⟨42,by decide⟩).lower ∧ (cell12999 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12999 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12999 ⟨43,by decide⟩).lower ∧ (cell12999 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12999 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12999 ⟨44,by decide⟩).lower ∧ (cell12999 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12999 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12999 ⟨45,by decide⟩).lower ∧ (cell12999 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12999 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12999 ⟨46,by decide⟩).lower ∧ (cell12999 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12999 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12999 ⟨47,by decide⟩).lower ∧ (cell12999 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12999 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12999 ⟨48,by decide⟩).lower ∧ (cell12999 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12999 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12999 ⟨49,by decide⟩).lower ∧ (cell12999 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12999 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12999 ⟨50,by decide⟩).lower ∧ (cell12999 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12999 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12999 ⟨51,by decide⟩).lower ∧ (cell12999 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12999 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12999 ⟨52,by decide⟩).lower ∧ (cell12999 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12999 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12999 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12999 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12999,cell12999,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12999 i).lower ∧
    (cell12999 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12999 i).upper ≤ (0.532 : ℝ) ∧
    (cell12999 i).centre ≤ (0.1 : ℝ) ∧ (cell12999 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12999 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12999 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12999

/-! The local source numeric instances at 12999 have no network premises. -/
namespace BstLean.Part269.N12999
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12999)
open BstLean.Part268 (cell12999)

noncomputable def sourceNumerics12999 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12999 (cell12999 i)
      scalarRow12999.M scalarRow12999.H scalarRow12999.xi := by
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
    energy_allowance := scalarRow12999.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12999]
    centre_nonneg := (scalarRow12999.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D25.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12999])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12999