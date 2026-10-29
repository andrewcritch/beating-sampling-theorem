import Mathlib

/-!
# Part 29, layer L2: the Gram term in raw coefficients

The coefficient sphere of part 29 is over the raw monomial coefficients of `m`: for the quadratic part
of component `k`, one coefficient `a k i j` per monomial `x_i x_j` with `i ≤ j`. The symmetric matrix is
`Q_ii = a_ii`, `Q_ij = Q_ji = a_ij / 2` (`i < j`). Then `tr(Q_k Q_l)` is the weighted inner product of the
raw coefficient vectors, with weight `1` on squares and `1/2` on cross monomials (the matrix `Λ`).
-/

namespace BstLean.Part29

variable {n : ℕ}

/-- The symmetric matrix of a quadratic form from its raw coefficients (entries with `i ≤ j` used). -/
noncomputable def symOfRaw (a : Fin n → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if i = j then a i i else if i < j then a i j / 2 else a j i / 2

theorem symOfRaw_isSymm (a : Fin n → Fin n → ℝ) : (symOfRaw a).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, symOfRaw]
  by_cases h : i = j
  · subst h; simp
  · rcases lt_or_gt_of_ne h with h' | h'
    · simp [h, Ne.symm h, h', not_lt.mpr h'.le]
    · simp [h, Ne.symm h, h', not_lt.mpr h'.le]

/-- **The Gram term in raw coefficients:** `tr(Q_k Q_l) = Σᵢ aᵢᵢ bᵢᵢ + ½ Σ_{i<j} aᵢⱼ bᵢⱼ`. -/
theorem trace_mul_symOfRaw (a b : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, symOfRaw a i j * symOfRaw b j i =
      ∑ i, a i i * b i i + (1 / 2) * ∑ i, ∑ j, (if i < j then a i j * b i j else 0) := by
  have hsplit : ∀ i j : Fin n, symOfRaw a i j * symOfRaw b j i =
      (if i = j then a i i * b i i else 0) + (1 / 4) * (if i < j then a i j * b i j else 0)
        + (1 / 4) * (if j < i then a j i * b j i else 0) := by
    intro i j
    simp only [symOfRaw]
    by_cases h : i = j
    · subst h; simp
    · rcases lt_or_gt_of_ne h with h' | h'
      · simp [h, Ne.symm h, h', not_lt.mpr h'.le]; ring
      · simp [h, Ne.symm h, h', not_lt.mpr h'.le]; ring
  simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hdiag : ∑ i : Fin n, ∑ j : Fin n, (if i = j then a i i * b i i else 0) = ∑ i, a i i * b i i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]; simp
  have hswap : ∑ i : Fin n, ∑ j : Fin n, (if j < i then a j i * b j i else 0) =
      ∑ i : Fin n, ∑ j : Fin n, (if i < j then a i j * b i j else 0) := Finset.sum_comm
  rw [hdiag, hswap]
  ring

end BstLean.Part29
