import BstLean.Part235Tails
import BstLean.Part235Junction
import BstLean.Part235Wide
import BstLean.Part235Core

/-! Part 235: a rational covariance enclosure under explicit radius and TI coefficients. -/
namespace BstLean.Part235
open Real BstLean.Part199

noncomputable def rationalCovarianceUpper (lam₀ lam₁ M : ℝ) : ℝ :=
  (528 / 1000) * (lam₁ * (5000 / 4999) + lam₀ * (500 / 473) * (121 / 10 ^ 4) +
    lam₀ * (10 / 9) * (409 / 10 ^ 4)) + M * (1028 / 10 ^ 6)

theorem radius_mean_factor_bound {n : ℕ} (hn : 11883 ≤ n) {θ : ℝ}
    (hθ : θ ≤ 528 / 1000) :
    (1 - 4 * θ / n)⁻¹ ≤ (5000 / 4999 : ℝ) := by
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith only [hnR]
  have hs : 4 * θ / (n : ℝ) ≤ (1 / 5000 : ℝ) := by
    rw [div_le_iff₀ hn0]
    linarith only [hθ, hnR]
  have hd : (4999 / 5000 : ℝ) ≤ 1 - 4 * θ / n := by linarith only [hs]
  rw [← one_div]
  exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd).trans (by norm_num)

/-- This enclosure uses exact analytic tail bounds. The two radius caps and the
TI coefficients are explicit inputs; no complete M1/M2 row is claimed. -/
theorem rational_covariance_bound {n : ℕ} (hn : 11883 ≤ n) {θ lam₀ lam₁ M b : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 528 / 1000)
    (hl₀ : 0 ≤ lam₀) (hl₁ : 0 ≤ lam₁) (hM : 0 ≤ M)
    (hr₀ : radiusMinus n θ exampleWide ≤ 1 / 10)
    (hr₁ : radiusMinus n θ exampleCore ≤ 54 / 1000)
    (hb : b ≤ 24 / 10 ^ 16) :
    jointCovScalar n θ exampleWide exampleCore lam₀ lam₁
      (1 - 4 * θ / n)⁻¹ M b ≤ rationalCovarianceUpper lam₀ lam₁ M := by
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
  have hp := mul_le_mul (mul_le_mul_of_nonneg_left hc hl₀) core_pair_bound hp0
    (by positivity : 0 ≤ lam₀ * (500 / 473))
  have ho := mul_le_mul (mul_le_mul_of_nonneg_left hw hl₀) core_outside_bound ho0
    (by positivity : 0 ≤ lam₀ * (10 / 9))
  have he := mul_le_mul_of_nonneg_left (radius_mean_factor_bound hn hθ) hl₁
  have hsum := add_le_add (add_le_add he hp) ho
  have hθsum := (mul_le_mul_of_nonneg_left hsum hθ0).trans
    (mul_le_mul_of_nonneg_right hθ (by positivity))
  have hx := mul_le_mul_of_nonneg_left (joint_exceptional_bound hb) hM
  exact add_le_add hθsum hx

/-- A rational sufficient condition is checked without assuming its analytic supply. -/
theorem rational_covariance_sufficient {lam₀ lam₁ M : ℝ}
    (hl₀ : lam₀ ≤ 65 / 100) (hl₁ : lam₁ ≤ 60 / 100) (hM : M ≤ 13 / 10) :
    rationalCovarianceUpper lam₀ lam₁ M ≤ (34 / 100 : ℝ) := by
  unfold rationalCovarianceUpper
  linarith only [hl₀, hl₁, hM]

/-- A complete conditional network conclusion. The numerical TI coefficients and
fourth-moment supply are visible premises, rather than proved M1/M2 data. -/
theorem cov_at_034_conditional {n : ℕ} (hn : 11883 ≤ n)
    (D : BstLean.Part157.Design n) (k : BstLean.Part157.Ret n)
    (hτ : 0 < D.tau0 k) {lam₀ lam₁ M b : ℝ}
    (hl₀ : 0 ≤ lam₀) (hl₁ : 0 ≤ lam₁) (hM : 0 ≤ M)
    (hl₀u : lam₀ ≤ 65 / 100) (hl₁u : lam₁ ≤ 60 / 100) (hMu : M ≤ 13 / 10)
    (hw : BstLean.Part150.thetaC k.1.2 (D.tau0 k) ∈ Set.Icc (46 / 100) (528 / 1000))
    (hb : b ≤ 24 / 10 ^ 16)
    (hX : BstLean.Part153.Xi4 k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) ≤
      M * (2 / (n : ℝ)) / n)
    (hC : ((k.1.2, D.tau0 k), (k.2.1.1.1, k.2.1.1.2)) ∈
      JointCovEvent n exampleWide exampleCore (46 / 100) (528 / 1000) lam₀ lam₁ b) :
    BstLean.Part160.COV_at D k (34 / 100) := by
  have hr₀ := (wide_radius_caps hn hw.1 hw.2).1
  have hr₁ := (core_radius_caps hn hw.1 hw.2).1
  apply cov_at_joint (by omega) D k hτ exampleWide exampleCore example_nested
    hl₀ hl₁ hM hw (by norm_num)
    (by linarith only [hr₀]) (by linarith only [hr₁]) hX hC
  exact (rational_covariance_bound hn (by linarith only [hw.1]) hw.2
    hl₀ hl₁ hM hr₀ hr₁ hb).trans (rational_covariance_sufficient hl₀u hl₁u hMu)

end BstLean.Part235
