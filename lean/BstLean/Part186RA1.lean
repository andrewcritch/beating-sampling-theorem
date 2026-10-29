import BstLean.Part184Mom
import BstLean.Part171Zeta

/-!
# Part 186 (file `RA1`): sums of independent polynomial rows (the row averaging of Lemma RA)

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, Lemma `t7:p08:RA` (row-averaged Taylor biases). For independent
rows `ζ_j = (ξ₁_j, ξ₂_j)` (two standard Gaussian coordinates) and a polynomial row bound
`q(R) = c₀ + c₁R + c₂R²` of `R = |ζ_j|²` with `c_i ≥ 0`, the sum `Σ_j q(R_j)` is `m μ` up to a
centred sum, `μ = E q(R) = c₀ + 2c₁ + 8c₂`. The centred part is paid by Part 184's `mom8_pi`.

* `two_point`: `(a + b)^{k+1} ≤ (1 + ε)^k a^{k+1} + (1 + 1/ε)^k b^{k+1}`.
* `int_RR_pow`: `E R^j = Σ_i C(j, i) E Z^{2i} E Z^{2(j−i)}` (and integrability).
* `lint_transfer`: the two Gaussian vectors `ξ₁, ξ₂` as one product over the rows.
* **`sum8_pi`**, **`sum4_pi`**: `E(Σ_j q(R_j))⁸ ≤ (1 + ε)⁷(mμ)⁸ + (1 + 1/ε)⁷M₈` and
  `E(Σ_j q(R_j))⁴ ≤ (1 + ε)³(mμ)⁴ + (1 + 1/ε)³(M₈/t + t)/2`, with an explicit crude `M₈`.
-/

namespace BstLean.Part186.RA

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)

/-- Two-point convexity of `x ↦ x^{k+1}`. -/
lemma two_point {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε) (k : ℕ) :
    (a + b) ^ (k + 1) ≤ (1 + ε) ^ k * a ^ (k + 1) + (1 + 1 / ε) ^ k * b ^ (k + 1) := by
  have h1 : (0 : ℝ) < 1 + ε := by linarith
  have hc := (convexOn_pow (k + 1)).2 (Set.mem_Ici.mpr (by positivity : (0 : ℝ) ≤ a * (1 + ε)))
    (Set.mem_Ici.mpr (by positivity : (0 : ℝ) ≤ b * (1 + 1 / ε)))
    (by positivity : (0 : ℝ) ≤ 1 / (1 + ε)) (by positivity : (0 : ℝ) ≤ ε / (1 + ε))
    (by field_simp)
  simp only [smul_eq_mul] at hc
  have e1 : 1 / (1 + ε) * (a * (1 + ε)) + ε / (1 + ε) * (b * (1 + 1 / ε)) = a + b := by
    field_simp; ring_nf
  rw [e1] at hc
  refine hc.trans (le_of_eq ?_)
  have e2 : (1 + 1 / ε) = (1 + ε) / ε := by field_simp; ring
  rw [e2, mul_pow, mul_pow, div_pow, div_pow, pow_succ (1 + ε), pow_succ ε]
  field_simp

/-- The one-dimensional standard Gaussian. -/
noncomputable abbrev g1 : Measure ℝ := gaussianReal 0 1

/-- The distribution of one row `(ξ₁_j, ξ₂_j)`. -/
noncomputable abbrev ρ2 : Measure (ℝ × ℝ) := g1.prod g1

/-- `R = |ζ|²`. -/
def RR (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + p.2 ^ 2

lemma RR_nonneg (p : ℝ × ℝ) : 0 ≤ RR p := by unfold RR; positivity

lemma measurable_RR : Measurable RR := by unfold RR; fun_prop

lemma int_RR_pow (j : ℕ) : Integrable (fun p => RR p ^ j) ρ2 ∧
    ∫ p, RR p ^ j ∂ρ2 = ∑ i ∈ Finset.range (j + 1),
      gaussMom (2 * i) * (j.choose i : ℝ) * gaussMom (2 * (j - i)) := by
  have e : ∀ p : ℝ × ℝ, RR p ^ j = ∑ i ∈ Finset.range (j + 1),
      (p.1 ^ (2 * i) * (j.choose i : ℝ)) * p.2 ^ (2 * (j - i)) := by
    intro p; unfold RR; rw [add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_mul, pow_mul]; ring
  have hi : ∀ i, Integrable (fun p : ℝ × ℝ =>
      (p.1 ^ (2 * i) * (j.choose i : ℝ)) * p.2 ^ (2 * (j - i))) ρ2 :=
    fun i => ((BstLean.Part130.integrable_pow_gauss (2 * i)).mul_const _).mul_prod
      (BstLean.Part130.integrable_pow_gauss _)
  simp_rw [e]
  refine ⟨integrable_finsetSum _ fun i _ => hi i, ?_⟩
  rw [integral_finsetSum _ fun i _ => hi i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_prod_mul (fun x : ℝ => x ^ (2 * i) * (j.choose i : ℝ))
    (fun y : ℝ => y ^ (2 * (j - i))), integral_mul_const, gaussMom_eq, gaussMom_eq]

lemma ER1 : ∫ p, RR p ∂ρ2 = 2 := by
  have h := (int_RR_pow 1).2
  simp only [pow_one] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, BstLean.Part171.gaussMom_two_mul]
  norm_num [Nat.choose, Nat.doubleFactorial]

lemma ER2 : ∫ p, RR p ^ 2 ∂ρ2 = 8 := by
  rw [(int_RR_pow 2).2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, BstLean.Part171.gaussMom_two_mul]
  norm_num [Nat.choose, Nat.doubleFactorial]

lemma ER4 : ∫ p, RR p ^ 4 ∂ρ2 = 384 := by
  rw [(int_RR_pow 4).2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, BstLean.Part171.gaussMom_two_mul]
  norm_num [Nat.choose, Nat.doubleFactorial]

lemma ER8 : ∫ p, RR p ^ 8 ∂ρ2 = 10321920 := by
  rw [(int_RR_pow 8).2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, BstLean.Part171.gaussMom_two_mul]
  norm_num [Nat.choose, Nat.doubleFactorial]

lemma ER12 : ∫ p, RR p ^ 12 ∂ρ2 = 1961990553600 := by
  rw [(int_RR_pow 12).2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, BstLean.Part171.gaussMom_two_mul]
  norm_num [Nat.choose, Nat.doubleFactorial]

lemma ER16 : ∫ p, RR p ^ 16 ∂ρ2 = 1371195958099968000 := by
  rw [(int_RR_pow 16).2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, BstLean.Part171.gaussMom_two_mul]
  norm_num [Nat.choose, Nat.doubleFactorial]

end BstLean.Part186.RA
