import BstLean.Part264DirectionError
import BstLean.Part253Direction

/-! The actual direction scalar has a uniform bound on the World window. -/
namespace BstLean.Part264
open Real Set MeasureTheory
open scoped ENNReal
open BstLean.Part130 BstLean.Part219 BstLean.Part215

theorem radius_nonneg_and_le {n : ℕ} (hn : 12225 ≤ n) (j : ℕ) (hj : j ≤ 96)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθhi : θ ≤ 54 / 100) :
    0 ≤ radiusCoefficient n j θ ∧ radiusCoefficient n j θ ≤ radiusCoefficient 12225 j θ := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hjR : (j : ℝ) ≤ 96 := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ 2 * j + 2 := by positivity
  have hc : (2 * j + 2 : ℝ) * θ / n ≤ 194 * (54 / 100 : ℝ) / 12225 := by gcongr <;> linarith
  have hc0 : (2 * j + 2 : ℝ) * θ / 12225 ≤ 194 * (54 / 100 : ℝ) / 12225 := by gcongr <;> linarith
  have hd : (2 * j + 2 : ℝ) * θ / n ≤ (2 * j + 2 : ℝ) * θ / 12225 := by gcongr
  unfold radiusCoefficient
  exact ⟨div_nonneg hθ (by linarith),
    div_le_div_of_nonneg_left hθ (by linarith) (by linarith)⟩

theorem amplitude_le {n : ℕ} (hn : 12225 ≤ n) {θ : ℝ}
    (hθ : 0 ≤ θ) (hθhi : θ ≤ 54 / 100) : paperAmplitude n θ ≤ paperAmplitude 12225 θ := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 4 * θ / n ≤ 4 * θ / 12225 := by gcongr
  have hnum : 0 ≤ 1 - θ := by linarith
  unfold paperAmplitude
  apply sqrt_le_sqrt
  exact div_le_div_of_nonneg_left hnum (by linarith) (by linarith)

theorem bias_le {n : ℕ} (hn : 12225 ≤ n) {θ : ℝ}
    (hθ : 0 ≤ θ) (hθhi : θ ≤ 54 / 100) : paperBias n θ ≤ paperBias 12225 θ := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hr := radius_nonneg_and_le hn 4 (by norm_num) hθ hθhi
  have hr0 := hr.1
  have hrle := hr.2
  have hrold0 := hr.1.trans hr.2
  unfold paperBias
  gcongr <;> positivity

theorem paperIdeal_le {n : ℕ} (hn : 12225 ≤ n) {θ e : ℝ}
    (hθ : 0 ≤ θ) (hθhi : θ ≤ 54 / 100) (he : 0 < e) :
    paperIdeal n θ e ≤ paperIdeal 12225 θ e := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hroot : √(12225 : ℝ) ≤ √(n : ℝ) := sqrt_le_sqrt hnR
  have h1 := radius_nonneg_and_le hn 1 (by norm_num) hθ hθhi
  have h24 := radius_nonneg_and_le hn 24 (by norm_num) hθ hθhi
  have h48 := radius_nonneg_and_le hn 48 (by norm_num) hθ hθhi
  have h96 := radius_nonneg_and_le hn 96 (by norm_num) hθ hθhi
  have h4 := radius_nonneg_and_le hn 4 (by norm_num) hθ hθhi
  have h40 := h4.1
  have h10 := h1.1
  have h240 := h24.1
  have h480 := h48.1
  have h960 := h96.1
  have h1le := h1.2
  have h24le := h24.2
  have h48le := h48.2
  have h96le := h96.2
  have h24old0 := h24.1.trans h24.2
  have h1old0 := h1.1.trans h1.2
  have h48old0 := h48.1.trans h48.2
  have h96old0 := h96.1.trans h96.2
  have ha := amplitude_le hn hθ hθhi
  have hb := bias_le hn hθ hθhi
  have hk := kernelSlope_nonneg (1 - θ)
  have hrot := BstLean.Part195.rotationConstant_nonneg 24
  have hb0 : 0 ≤ paperBias n θ := by unfold paperBias; positivity
  have hbold0 := hb0.trans hb
  have ha0 : 0 ≤ paperAmplitude n θ := sqrt_nonneg _
  have haold0 : 0 ≤ paperAmplitude 12225 θ := sqrt_nonneg _
  unfold paperIdeal
  gcongr <;> positivity

theorem ideal_window {n : ℕ} (hn : 12225 ≤ n) {θ e : ℝ}
    (hw : θ ∈ Icc (0.47199 : ℝ) 0.52358) (he : 0.665 ≤ e) : paperIdeal n θ e ≤ 0.230 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  exact (paperIdeal_le hn hθ (hw.2.trans (by norm_num)) (by linarith)).trans
    (BstLean.Part253.ideal_window hw he)

theorem direction_budget_le {n : ℕ} (hn : 12225 ≤ n)
    (c : Fin n → ℝ) (τ e xi eta : ℝ) (δ : ℝ≥0∞)
    (hw : BstLean.Part150.thetaC c τ ∈ Icc (0.47199 : ℝ) 0.52358)
    (he : 0.665 ≤ e) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.1)
    (hop : operatorAllowance c τ eta δ ^ 2 ≤ 1.22) :
    paperDirectionBudget c τ e xi eta δ ≤ (0.08955 : ℝ) := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  let θ := BstLean.Part150.thetaC c τ
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hθ1 : θ ≤ 0.52358 := hw.2
  have hrad := radius_nonneg_and_le hn 12 (by norm_num) hθ (hθ1.trans (by norm_num))
  have hR : radiusCoefficient n 12 θ ≤ 0.525 := hrad.2.trans
    (BstLean.Part253.radius_upper 12 hθ hw.2 (by norm_num) (by norm_num))
  have hRs : √(radiusCoefficient n 12 θ / e) ≤ 0.889 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (div_le_div₀ (by norm_num) hR (by norm_num) he).trans (by norm_num)
  have heps := error_epsilon_upper hn
  have heps0 := BstLean.Part209.meanEpsilon_nonneg n 16
    (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num : (1 / 100 : ℝ) < 1)
  have hEp0 : 0 ≤ BstLean.Part209.pairEpsilon n 16 (1 / 100) :=
    add_nonneg heps0 (BstLean.Part209.fluctuationRoot_nonneg _ _)
  have hroot : (0.88 : ℝ) ≤ (7 / 25000 : ℝ) ^ (1 / 64 : ℝ) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by positivity)
    have hh := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 7 / 25000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hh
    rw [hh]
    norm_num
  have htransfer : √(operatorAllowance c τ eta δ ^ 2 * xi / ((n : ℝ) * e)) ≤ 0.00388 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1.22 : ℝ) * 0.1 / (12225 * 0.665) := by gcongr
      _ ≤ (0.00388 : ℝ)^2 := by norm_num
  have hi := ideal_window hn hw he
  have hi0 : 0 ≤ paperIdeal n θ e := by
    have hr (j : ℕ) (hj : j ≤ 96) :=
      (radius_nonneg_and_le hn j hj hθ (hθ1.trans (by norm_num))).1
    have hr48 := hr 48 (by norm_num)
    have hr96 := hr 96 (by norm_num)
    have hr4 := hr 4 (by norm_num)
    have hk := kernelSlope_nonneg (1 - θ)
    have hrot := BstLean.Part195.rotationConstant_nonneg 24
    unfold paperIdeal paperAmplitude paperBias
    positivity
  unfold paperDirectionBudget
  change (paperIdeal n θ e + _ + _) ^ 2 ≤ _
  calc
    _ ≤ ((0.230 : ℝ) + 0.0647 * 0.889 / 0.88 + 0.00388)^2 := by gcongr
    _ ≤ (0.08955 : ℝ) := by norm_num

end BstLean.Part264
