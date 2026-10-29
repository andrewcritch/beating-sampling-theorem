import BstLean.Part56Defs

/-!
# Part 69, wave 0: definitions — the single-use moment program at `d_M = d_f = 2`

Role: `delegations/statements/p69-spec.md`. Source: `delegations/answers/omSU-cx-disprover.md`,
`delegations/answers/omSU-opus-prover.md`.

At `k = d = 2` the line program `pg` of Part 56 reads only the keys `(i, l, j⃗)` with `2l ≤ i`.
Their surrogate weights are explicit rational functions of
* `a = E_Q s²`, `b = E_Q s⁴` (`s = v·x`, `Q = surrRK n K t v`), which are ratios of finite sums
  `Z_l = Σ_{j ≤ K} (t^j/j!) U_{j+l}`, `U_j = E_σ s^{2j} = Π_{i<j} (2i+1)/(n+2i)`;
* the power sums `q = Σ v_i⁴`, `r = Σ v_i⁶`;
* `n`.

This file holds definitions only.
-/

namespace BstLean.Part69

open BstLean.Part56

variable {n : ℕ}

/-- `U_j = Π_{i<j} (2i+1)/(n+2i)` (the uniform-sphere moment `E_σ s^{2j}`). -/
noncomputable def U69 (n j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j, ((2 * (i : ℝ) + 1) / ((n : ℝ) + 2 * (i : ℝ)))

/-- `Z_l = Σ_{j ≤ K} (t^j/j!) U_{j+l}`. -/
noncomputable def Z69 (n K : ℕ) (t : ℝ) (l : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1), t ^ j / (j.factorial : ℝ) * U69 n (j + l)

/-- `a = Z_1/Z_0 = E_Q s²`. -/
noncomputable def a69 (n K : ℕ) (t : ℝ) : ℝ := Z69 n K t 1 / Z69 n K t 0

/-- `b = Z_2/Z_0 = E_Q s⁴`. -/
noncomputable def b69 (n K : ℕ) (t : ℝ) : ℝ := Z69 n K t 2 / Z69 n K t 0

/-- `q = Σ v_i⁴`. -/
noncomputable def q69 (v : Fin n → ℝ) : ℝ := ∑ i, v i ^ 4

/-- `r = Σ v_i⁶`. -/
noncomputable def r69 (v : Fin n → ℝ) : ℝ := ∑ i, v i ^ 6

/-! ## The moment-level formulas (`m = n − 1`) -/

/-- `E w`, `w = Σ v_i² x_i²`: `q a + (1−q)(1−a)/m`. -/
noncomputable def Ew69 (n : ℕ) (a q : ℝ) : ℝ := q * a + (1 - q) * (1 - a) / ((n : ℝ) - 1)

/-- `E s² w`: `q b + (1−q)(a−b)/m`. -/
noncomputable def Esw69 (n : ℕ) (a b q : ℝ) : ℝ := q * b + (1 - q) * (a - b) / ((n : ℝ) - 1)

/-- `E w²`: `q² b + (2q(1−q) + 4(r−q²))(a−b)/m + ((1−q)² + 2(q−2r+q²))(1−2a+b)/(m(m+2))`. -/
noncomputable def Ew2_69 (n : ℕ) (a b q r : ℝ) : ℝ :=
  q ^ 2 * b + (2 * q * (1 - q) + 4 * (r - q ^ 2)) * (a - b) / ((n : ℝ) - 1) +
    ((1 - q) ^ 2 + 2 * (q - 2 * r + q ^ 2)) * (1 - 2 * a + b) / (((n : ℝ) - 1) * ((n : ℝ) + 1))

/-- `E Σ x_i⁴`: `q b + 6(1−q)(a−b)/m + 3(n−2+q)(1−2a+b)/(m(m+2))`. -/
noncomputable def Eq4_69 (n : ℕ) (a b q : ℝ) : ℝ :=
  q * b + 6 * (1 - q) * (a - b) / ((n : ℝ) - 1) +
    3 * ((n : ℝ) - 2 + q) * (1 - 2 * a + b) / (((n : ℝ) - 1) * ((n : ℝ) + 1))

/-- `E (s² + w)² = b + 2 E s²w + E w²`. -/
noncomputable def Esq69 (n : ℕ) (a b q r : ℝ) : ℝ := b + 2 * Esw69 n a b q + Ew2_69 n a b q r

/-- `A = E β₂ = (a + E w)/(1 + q)`. -/
noncomputable def A69 (n : ℕ) (a q : ℝ) : ℝ := (a + Ew69 n a q) / (1 + q)

/-- `H = E β₂² = E(s² + w)²/(1 + q)²`. -/
noncomputable def H69 (n : ℕ) (a b q r : ℝ) : ℝ := Esq69 n a b q r / (1 + q) ^ 2

/-- `R = E τ = 3/2 − a + E Σx_i⁴/2 − E(s² + w)²/(2(1 + q))`. -/
noncomputable def R69 (n : ℕ) (a b q r : ℝ) : ℝ :=
  3 / 2 - a + Eq4_69 n a b q / 2 - Esq69 n a b q r / (2 * (1 + q))

/-- The moment `E[s^{c₁} β₂^{c₂}]` for `c₁ + c₂ ≤ 2` (the odd ones vanish); `0` otherwise. -/
noncomputable def momC69 (n : ℕ) (a b q r : ℝ) (c1 c2 : ℕ) : ℝ :=
  if c1 = 0 ∧ c2 = 0 then 1
  else if c1 = 0 ∧ c2 = 1 then A69 n a q
  else if c1 = 2 ∧ c2 = 0 then a
  else if c1 = 0 ∧ c2 = 2 then H69 n a b q r
  else 0

/-- The number of letters equal to `j` in the word of a key. -/
def cnt69 {k d : ℕ} (κ : KeyRK k d) (j : Fin (d + 1)) : ℕ :=
  (Finset.univ.filter fun r => κ.2 r = j).card

/-- The weights, as functions of `(a, b, q, r)`: for `l = 0`, `E Π_r β_{j_r} = E[s^{c₁} β₂^{c₂}]`
(`β₀ = 1`, `β₁ = s`); for `(i, l) = (2, 1)`, `σ² E τ = R/𝒟`; `0` at the keys `2l > i` that `pg`
never reads. -/
noncomputable def wF69 (n : ℕ) (a b q r : ℝ) (κ : KeyRK 2 2) : ℝ :=
  if (κ.1.2 : ℕ) = 0 then momC69 n a b q r (cnt69 κ 1) (cnt69 κ 2)
  else if (κ.1.1 : ℕ) = 2 ∧ (κ.1.2 : ℕ) = 1 then
    R69 n a b q r / ((n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2)
  else 0

/-- The weights at `(t, v)`. -/
noncomputable def w69 (n K : ℕ) (t : ℝ) (v : Fin n → ℝ) (κ : KeyRK 2 2) : ℝ :=
  wF69 n (a69 n K t) (b69 n K t) (q69 v) (r69 v) κ

end BstLean.Part69
