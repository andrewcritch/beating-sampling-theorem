import BstLean.Part141Atom

/-!
# Part 150, item 1: the binomial atoms and weights, and their moments

Role: `delegations/statements/p150-spec.md`, item 1. Paper source: `onW45-opus-prover.md` §1
("Atoms"), `onW25c-cx.md` §3 (the exact moments).

`Z_J = (ξ_1 + … + ξ_J)/√J` with independent signs `ξ_i`. Its atoms are `(2j − J)/√J` and its
weights are `C(J, j)/2^J`, `j = 0, …, J`.

* `walkMean J g = Σ_j C(J, j)/2^J · g(2j − J)`: the mean of `g(ξ_1 + … + ξ_J)`.
* `binW J j = C(J, j)/2^J`, `binAtom J j = (2j − J)/√J`,
  `binMean J f = Σ_{j ≤ J} binW J j · f(binAtom J j)`: the mean of `f(Z_J)`.
* `walkMean_succ`: the recursion `E g(S_{J+1}) = (E g(S_J + 1) + E g(S_J − 1))/2`.
The moments and the characteristic function are in `Part150Mom`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open Finset
open BstLean.Part130 BstLean.Part137

/-- The mean of `g(ξ_1 + … + ξ_J)` for independent signs `ξ_i`. -/
noncomputable def walkMean (J : ℕ) (g : ℝ → ℝ) : ℝ :=
  ∑ j ∈ range (J + 1), (J.choose j : ℝ) / 2 ^ J * g (2 * (j : ℝ) - J)

/-- The binomial weight `C(J, j)/2^J`. -/
noncomputable def binW (J j : ℕ) : ℝ := (J.choose j : ℝ) / 2 ^ J

/-- The binomial atom `(2j − J)/√J`. -/
noncomputable def binAtom (J j : ℕ) : ℝ := (2 * (j : ℝ) - J) / √(J : ℝ)

/-- **The binomial mean** `E f(Z_J) = Σ_{j ≤ J} C(J, j)/2^J · f((2j − J)/√J)`. -/
noncomputable def binMean (J : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ j ∈ range (J + 1), binW J j * f (binAtom J j)

lemma binMean_eq_walk (J : ℕ) (f : ℝ → ℝ) :
    binMean J f = walkMean J (fun k => f (k / √(J : ℝ))) := rfl

lemma binW_nonneg (J j : ℕ) : 0 ≤ binW J j := by unfold binW; positivity

lemma walkMean_zero (g : ℝ → ℝ) : walkMean 0 g = g 0 := by
  simp [walkMean]

/-- The recursion: one more sign. -/
theorem walkMean_succ (J : ℕ) (g : ℝ → ℝ) :
    walkMean (J + 1) g = (walkMean J (fun k => g (k + 1)) + walkMean J (fun k => g (k - 1))) / 2 := by
  unfold walkMean
  have h1 : ∑ j ∈ range (J + 1 + 1), ((J + 1).choose j : ℝ) / 2 ^ (J + 1) * g (2 * (j : ℝ) - (J + 1 : ℕ))
      = ∑ j ∈ range (J + 1), ((J + 1).choose (j + 1) : ℝ) / 2 ^ (J + 1) * g (2 * ((j + 1 : ℕ) : ℝ) - (J + 1 : ℕ))
        + 1 / 2 ^ (J + 1) * g (-(J + 1 : ℕ)) := by
    rw [sum_range_succ']
    simp
  rw [h1]
  have h2 : ∑ j ∈ range (J + 1), ((J + 1).choose (j + 1) : ℝ) / 2 ^ (J + 1) * g (2 * ((j + 1 : ℕ) : ℝ) - (J + 1 : ℕ))
      = ∑ j ∈ range (J + 1), (J.choose j : ℝ) / 2 ^ (J + 1) * g (2 * (j : ℝ) - J + 1)
        + ∑ j ∈ range (J + 1), (J.choose (j + 1) : ℝ) / 2 ^ (J + 1) * g (2 * ((j + 1 : ℕ) : ℝ) - J - 1) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [Nat.choose_succ_succ]
    push_cast
    have e1 : (2 * ((j : ℝ) + 1) - ((J : ℝ) + 1)) = 2 * (j : ℝ) - J + 1 := by ring
    have e2 : (2 * ((j : ℝ) + 1) - (J : ℝ) - 1) = 2 * (j : ℝ) - J + 1 := by ring
    rw [e1, e2]
    ring
  rw [h2]
  have h3 : ∑ j ∈ range (J + 1), (J.choose (j + 1) : ℝ) / 2 ^ (J + 1) * g (2 * ((j + 1 : ℕ) : ℝ) - J - 1)
        + 1 / 2 ^ (J + 1) * g (-(J + 1 : ℕ))
      = ∑ j ∈ range (J + 1), (J.choose j : ℝ) / 2 ^ (J + 1) * g (2 * (j : ℝ) - J - 1) := by
    have := sum_range_succ' (fun j : ℕ => (J.choose j : ℝ) / 2 ^ (J + 1) * g (2 * (j : ℝ) - J - 1)) (J + 1)
    rw [sum_range_succ] at this
    simp only [Nat.choose_succ_self, Nat.cast_zero, zero_div, zero_mul, add_zero, Nat.choose_zero_right,
      Nat.cast_one, mul_zero, zero_sub] at this
    rw [this]
    push_cast
    congr 2
    ring_nf
  rw [add_assoc, h3, add_div, sum_div, sum_div]
  congr 1 <;> refine sum_congr rfl fun j _ => ?_ <;> rw [pow_succ] <;> field_simp

end BstLean.Part150
