import BstLean.Part264PilotSourcePrelude
import BstLean.Part253FiniteCentre
import BstLean.Part253Exp
import BstLean.Part211MA

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264
open BstLean.Part253
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036502 : ℝ) ≤ wn 12226 := by
  have hn : √(12226 : ℝ) ≤ 110.571245 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12226 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.571245 ≤ 2 / √12226 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_cs_upper : csC ≤ 1.295212 := by
  have hp := pi_lt_d6.le
  have hd : (1 : ℝ) / 3.141593 ≤ 1 / π := by gcongr
  unfold csC
  linarith

theorem pilot_rho_bounds : (0.00026182 : ℝ) ≤ rhoBar 12226 csC ∧
    rhoBar 12226 csC ≤ 0.00026185 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := pilot_cs_upper
  have hc0 : 0 < csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036502 : ℝ) / (1.295212 * 12226) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12226) := by gcongr
      _ ≤ (0.00026185 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12226 csC) ≤ 0.00104747 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12226 csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12226 csC) :=
    le_sqrt_of_sq_le (by linarith)
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √2 ≤ 0.707106782 := by
    calc
      _ ≤ (1 : ℝ) / 1.414213562 := by gcongr
      _ ≤ (0.707106782 : ℝ) := by norm_num
  have hgap : (0.292631318 : ℝ) ≤ √(1 - 2 * rhoBar 12226 csC) - 1 / √2 := by linarith
  have hexp : (100 : ℝ) ≤ (√(1 - 2 * rhoBar 12226 csC) - 1 / √2) ^ 2 /
      (2 * rhoBar 12226 csC) := by
    apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12226 csC)).mpr
    nlinarith
  have h := exp_negative_bound 100 (by norm_num : ((2.71828 : ℝ) ^ 100)⁻¹ ≤ 1 / 10 ^ 40)
  unfold piBar
  apply le_trans ?_ h
  apply exp_le_exp.mpr
  norm_num only [Nat.cast_ofNat]
  linarith

theorem pilot_phi_zero_upper : phiG 0 ≤ 0.399 := by
  have hs : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith [pi_gt_d6])
  unfold phiG
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, neg_zero, exp_zero, mul_one]
  have h := (inv_le_inv₀ (by positivity : 0 < √(2 * π)) (by norm_num : (0 : ℝ) < 2.506628)).mpr hs
  exact h.trans (by norm_num)

theorem pilot_phi_one_upper : phiG 1 ≤ 0.243 := by
  have hz := pilot_phi_zero_upper
  have he := exp_half_lower
  have he' : exp (-(1 / 2 : ℝ)) ≤ (1.6487 : ℝ)⁻¹ := by
    rw [exp_neg]
    exact (inv_le_inv₀ (exp_pos _) (by norm_num)).mpr he
  have hid : phiG 1 = phiG 0 * exp (-(1 / 2 : ℝ)) := by
    unfold phiG
    norm_num
  rw [hid]
  calc
    _ ≤ (0.399 : ℝ) * (1.6487 : ℝ)⁻¹ :=
      mul_le_mul hz he' (exp_pos _).le (by norm_num)
    _ ≤ (0.243 : ℝ) := by norm_num

theorem pilot_cc_bounds : cc0 (rhoBar 12226 csC) (piBar (rhoBar 12226 csC)) ≤ 0.00020001 ∧
    cc1 (rhoBar 12226 csC) (piBar (rhoBar 12226 csC)) ≤ 0.00012727 ∧
    cc2 (rhoBar 12226 csC) ≤ 0.00007388 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12226 csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12226 csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12226 csC) := by unfold piBar; positivity
  have hz := pilot_phi_zero_upper
  have ho := pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12226 csC * nuR (rhoBar 12226 csC)) ≤ 0.00052372 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.00026185 : ℝ) * 0.00104747 := by gcongr
      _ ≤ (0.00052372 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12226 csC) * nuR (rhoBar 12226 csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.00104747 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12226 csC) * rhoBar 12226 csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.00026185 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.00026185 / 2 + 0.399 * 0.00104747 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.00020001 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.00052372 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.00012727 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.00026185 / 1.414213562 := by gcongr
      _ ≤ (0.00007388 : ℝ) := by norm_num

end BstLean.Part264
