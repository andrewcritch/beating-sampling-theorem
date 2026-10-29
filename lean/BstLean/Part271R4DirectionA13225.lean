import BstLean.Part271R4DirectionA13225Error
import BstLean.Part271R4DirectionA13225Ideal

/-! Direction budget transferred from the block's lower endpoint. -/
namespace BstLean.Part271.R4.A13225
open Real Set BstLean.Part219 BstLean.Part215
open scoped ENNReal

theorem direction {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)
    (c : Fin n → ℝ) (τ e xi eta : ℝ) (δ : ℝ≥0∞)
    (hw : BstLean.Part150.thetaC c τ ∈ Icc (0.47199 : ℝ) 0.52358)
    (he : 0.665 ≤ e) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.1)
    (hop : operatorAllowance c τ eta δ ^ 2 ≤ 1.22) :
    paperDirectionBudget c τ e xi eta δ ≤ (8639390951/100000000000) := by
  have hroot : (0.88 : ℝ) ≤ (7/25000 : ℝ) ^ (1/64 : ℝ) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by positivity)
    have h := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 7/25000) (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at h
    rw [h]
    norm_num
  have hRc : ∀ θ ∈ Icc (0.47199 : ℝ) 0.52358, radiusCoefficient 13225 12 θ ≤ 0.525 := by
    intro θ hθ
    have ht0 : 0 ≤ θ := (by norm_num : (0 : ℝ) ≤ 0.47199).trans hθ.1
    have hm := (BstLean.Part277.radius_nonneg_and_leP (n0 := 12225)
      (by norm_num) (by norm_num : 12225 ≤ 13225) 12 (by norm_num)
      ht0 (hθ.2.trans (by norm_num))).2
    exact hm.trans (BstLean.Part253.radius_upper 12 ht0 hθ.2 (by norm_num) (by norm_num))
  have h := BstLean.Part277.direction_budget_leP (n0 := 13225) (by norm_num) ha
    c τ e xi eta δ (e0 := 0.665) (xi0 := 0.1) (MP := 1.22)
    (I0 := (28495578659/125000000000)) (ε0 := (61455259841/1000000000000))
    (Rc := 0.525) (sR := 0.889) (ρ0 := 0.88)
    (by norm_num) hw (by norm_num) (by norm_num) he hxi hxi1 hop (by norm_num)
    (fun θ hθ e' he' => direction_ideal_window ha hb hθ he') hRc
    ((direction_error ha hb).2.trans (by norm_num)) (by norm_num) (by norm_num) (by norm_num) hroot
  have hs : √((1.22 : ℝ) * 0.1 / (((13225 : ℕ) : ℝ) * 0.665)) ≤ 0.00388 := sqrt_le_iff.mpr (by norm_num)
  apply h.trans
  calc
    _ ≤ ((28495578659/125000000000) + (61455259841/1000000000000) * (0.889 : ℝ) / 0.88 + 0.00388)^2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part271.R4.A13225
