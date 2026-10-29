import BstLean.Part238M12Net
import BstLean.Part235Scalar

/-! Part 238: a conditional M1/M2 covariance conclusion with the sharp core coefficient.
The TI constants, the TI hypotheses and the fourth-moment coefficient are visible premises.
No M1/M2 TI constant is certified here. -/
namespace BstLean.Part238
open MeasureTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part157 BstLean.Part160 BstLean.Part182
  BstLean.Part208
open BstLean.Part199 (Window radiusMinus exampleCore exampleWide example_nested pairRowBound
  outsideBound)
open BstLean.Part150 (thetaC)
open BstLean.Part153 (nrm Xi4)

/-- The exceptional factor with mass `2e^{-32} + 2b` and `b ≤ 2.4·10⁻¹⁵` is at most `.001028`. -/
theorem sharp_exceptional_bound {b : ℝ} (hb : b ≤ 24 / 10 ^ 16) :
    2 * √(√(2 * exp (-exampleWide.pair ^ 2 / 2) + 2 * b)) + √(outsideBound exampleWide) ≤
      (1028 / 10 ^ 6 : ℝ) := by
  have hp : 2 * exp (-exampleWide.pair ^ 2 / 2) ≤ (26 / 10 ^ 15 : ℝ) := by
    simpa only [exampleWide] using BstLean.Part182.two_exp_neg32
  have hq : √(√(2 * exp (-exampleWide.pair ^ 2 / 2) + 2 * b)) ≤ (420 / 10 ^ 6 : ℝ) := by
    apply BstLean.Part182.sqrt_sqrt_le_of (by norm_num)
    linarith only [hp, hb]
  have ho : √(outsideBound exampleWide) ≤ (188 / 10 ^ 6 : ℝ) := by
    apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
    linarith only [BstLean.Part235.wide_outside_bound]
  linarith only [hq, ho]

/-- The sharp scalar has the Part 235 rational upper bound with `λ₁` replaced by the core
coefficient `K`. -/
theorem sharp_rational_bound {n : ℕ} (hn : 11883 ≤ n) {θ lam₀ K M b : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 528 / 1000) (hl₀ : 0 ≤ lam₀) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hr₀ : radiusMinus n θ exampleWide ≤ 1 / 10)
    (hr₁ : radiusMinus n θ exampleCore ≤ 54 / 1000) (hb : b ≤ 24 / 10 ^ 16) :
    sharpScalar n θ exampleWide exampleCore K lam₀ (1 - 4 * θ / n)⁻¹ M
      (2 * exp (-exampleWide.pair ^ 2 / 2) + 2 * b) ≤
      BstLean.Part235.rationalCovarianceUpper lam₀ K M := by
  have hw : (1 - radiusMinus n θ exampleWide)⁻¹ ≤ (10 / 9 : ℝ) := by
    rw [← one_div]
    exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 9 / 10)
      (by linarith only [hr₀])).trans (by norm_num)
  have hc : (1 - radiusMinus n θ exampleCore)⁻¹ ≤ (500 / 473 : ℝ) := by
    rw [← one_div]
    exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 473 / 500)
      (by linarith only [hr₁])).trans (by norm_num)
  have hp0 : 0 ≤ pairRowBound exampleCore := by unfold pairRowBound; positivity
  have ho0 : 0 ≤ outsideBound exampleCore := by unfold outsideBound; positivity
  have hp := mul_le_mul (mul_le_mul_of_nonneg_left hc hl₀) BstLean.Part235.core_pair_bound hp0
    (by positivity : 0 ≤ lam₀ * (500 / 473))
  have ho := mul_le_mul (mul_le_mul_of_nonneg_left hw hl₀) BstLean.Part235.core_outside_bound
    ho0 (by positivity : 0 ≤ lam₀ * (10 / 9))
  have he := mul_le_mul_of_nonneg_left (BstLean.Part235.radius_mean_factor_bound hn hθ) hK
  have hsum := add_le_add (add_le_add he hp) ho
  have hθsum := (mul_le_mul_of_nonneg_left hsum hθ0).trans
    (mul_le_mul_of_nonneg_right hθ (by positivity))
  have hx := mul_le_mul_of_nonneg_left (sharp_exceptional_bound hb) hM
  unfold sharpScalar BstLean.Part235.rationalCovarianceUpper
  linarith only [hθsum, hx]

/-- **Conditional M1/M2 covariance bound `.34` with the sharp core coefficient.** On the joint
event with cutoff `b ≤ 2.4·10⁻¹⁵`, the bounds `λ₀ ≤ .65`,
`min(kE + 1.4284 ko + .51 ks, λ₁) ≤ .60` and `M ≤ 1.3` give `COV_at D k .34`. -/
theorem cov_at_034_sharp_M12 {n : ℕ} (hn : 11883 ≤ n) (D : Design n) (k : Ret n)
    (hτ : 0 < D.tau0 k) {kE ko ks lam₀ M b : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (hl₀ : 0 ≤ lam₀) (hM : 0 ≤ M) (hl₀u : lam₀ ≤ 65 / 100)
    (hKu : min (kE + 14284 / 10000 * ko + 51 / 100 * ks) (ta_lam kE ko ks) ≤ 60 / 100)
    (hMu : M ≤ 13 / 10)
    (hw : thetaC k.1.2 (D.tau0 k) ∈ Set.Icc (46 / 100) (528 / 1000))
    (hb : b ≤ 24 / 10 ^ 16)
    (hX : Xi4 k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) ≤ M * (2 / (n : ℝ)) / n)
    (hC : ((k.1.2, D.tau0 k), (k.2.1.1.1, k.2.1.1.2)) ∈
      SharpCovEvent n exampleWide exampleCore (46 / 100) (528 / 1000) lam₀ kE ko ks (63 / 100) b) :
    COV_at D k (34 / 100) := by
  have hr₀ := (BstLean.Part235.wide_radius_caps hn hw.1 hw.2).1
  have hr₁ := (BstLean.Part235.core_radius_caps hn hw.1 hw.2).1
  have hsq : √(51 / 100 : ℝ) ≤ 7142 / 10000 :=
    BstLean.Part182.sqrt_le_of_sq' (by norm_num) (by norm_num)
  have hK1 : sharpK kE ko ks (51 / 100) ≤ kE + 14284 / 10000 * ko + 51 / 100 * ks := by
    unfold sharpK
    have := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * ko)
    linarith
  have hKmin : min (sharpK kE ko ks (51 / 100)) (ta_lam kE ko ks) ≤ 60 / 100 :=
    (min_le_min_right _ hK1).trans hKu
  have hK0 : 0 ≤ min (sharpK kE ko ks (51 / 100)) (ta_lam kE ko ks) :=
    le_min (sharpK_nonneg hkE hko hks (by norm_num)) (ta_lam_nonneg hkE hks)
  refine cov_at_sharp_M12 hn D k hτ hkE hko hks hl₀ hM hw hX hC ?_
  exact (sharp_rational_bound hn (by linarith only [hw.1]) hw.2 hl₀ hK0 hM hr₀ hr₁ hb).trans
    (BstLean.Part235.rational_covariance_sufficient hl₀u hKmin hMu)

end BstLean.Part238
