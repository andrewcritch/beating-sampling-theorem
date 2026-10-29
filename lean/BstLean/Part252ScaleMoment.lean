import BstLean.Part252LatitudeMoments
import BstLean.Part162VS

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12225 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12225)
    (p : Ix 12225 × (Fin (12225 - 1) → ℝ)) :
    sgA (paperDesignP 12225) c p.1 p.2 ^ 2 ≤
      (2 / (12225 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12225).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12225) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12225 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12225 : ℝ) * _ ≤ 2 / 12225 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12225)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12225}
    (hw : WINDOW (paperDesignP 12225) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12225) c a v ^ 8
      ∂stdGauss (Fin (12225 - 1)) ∂muI 12225 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12225).prod (stdGauss (Fin (12225 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12225) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12225) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12225 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12225) c p.1 p.2)
      (√(2 / (12225 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12225)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12225 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12225) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 12225}
    (hw : WINDOW (paperDesignP 12225) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12225) c a v -
      ∫ w, sA (paperDesignP 12225) c a w ∂stdGauss (Fin (12225 - 1))) ^ 2
      ∂stdGauss (Fin (12225 - 1))) ^ 2 ∂muI 12225 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12225) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part252
