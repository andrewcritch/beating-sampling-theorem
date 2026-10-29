import BstLean.Part74Defs

/-!
# Part 74: the engine output as a function of the table sums, and the weights at `(3, 3)`

* `TrmN = ℕ × ℕ × Mon`: a term `c · s^e · Π_{(a,b) ∈ M} S_{a,b}`, `s = S_{1,1}`; lists of terms are
  polynomials. `mulL`, `powL`: product and power of lists.
* `ILF p W Z0 f g D L`: the surrogate expectation of the polynomial `L` (all degrees even and
  `≤ 2D`), as a function of the power sums `p`, the table sums `W c q` and `Z0`:
  `Σ_{q ≤ D} Σ_{c ≤ q} (2^c/(2c)!) · E_g[∂_v^{2c} L_{2q}] · W_{c,q} / Z_0` (Theorem S′), where
  `L_{2q}` is the part of degree `2q`.
* `w33F`, `w33`: the weights of the line program at `(d_M, d_f) = (3, 3)`.
-/

namespace BstLean.Part74

open BstLean.Part56
open BstLean.Part69 (Z69 cnt69)

variable {n : ℕ}

/-- A term `c · s^e · Π_{(a,b) ∈ M} S_{a,b}`. -/
abbrev TrmN := ℕ × ℕ × Mon

/-- The `x`-degree of a term. -/
def tdeg (t : TrmN) : ℕ := t.2.1 + mdeg t.2.2

/-- The product of two terms. -/
def mulT (s t : TrmN) : TrmN := (s.1 * t.1, s.2.1 + t.2.1, s.2.2 ++ t.2.2)

/-- The product of two polynomials. -/
def mulL (L1 L2 : List TrmN) : List TrmN := L1.flatMap fun s => L2.map (mulT s)

/-- The power of a polynomial. -/
def powL (L : List TrmN) : ℕ → List TrmN
  | 0 => [(1, 0, [])]
  | k + 1 => mulL L (powL L k)

/-- `E_g[∂_v^c L(g)]` for a polynomial `L`. -/
def dvEsL {R : Type} [CommRing R] (p : ℕ → R) (f g c : ℕ) (L : List TrmN) : R :=
  (L.map fun t => (t.1 : R) * dvEs p f g c t.2.1 t.2.2).sum

/-- The engine output: the surrogate expectation of `L`, from `p`, `W`, `Z0`. -/
noncomputable def ILF (p : ℕ → ℝ) (W : ℕ → ℕ → ℝ) (Z0 : ℝ) (f g D : ℕ) (L : List TrmN) : ℝ :=
  (∑ q ∈ Finset.range (D + 1), ∑ c ∈ Finset.range (q + 1),
    (2 : ℝ) ^ c / ((2 * c).factorial : ℝ) *
      dvEsL p f g (2 * c) (L.filter fun t => tdeg t = 2 * q) * W c q) / Z0

/-- The engine output at `(n, K, t, v)`. -/
noncomputable def IL74 (n K : ℕ) (t : ℝ) (v : Fin n → ℝ) (f g D : ℕ) (L : List TrmN) : ℝ :=
  ILF (pw v) (W74 n K t) (Z69 n K t 0) f g D L

/-! ## The line program at `(3, 3)` -/

/-- `s`. -/
def sL33 : List TrmN := [(1, 1, [])]
/-- `s² + S_{2,2}`, the numerator of `β₂`. -/
def N2L : List TrmN := [(1, 2, []), (1, 0, [(2, 2)])]
/-- `s³ + 3 s S_{2,2} + 2 S_{3,3}`, the numerator of `β₃`. -/
def N3L : List TrmN := [(1, 3, []), (3, 1, [(2, 2)]), (2, 0, [(3, 3)])]
/-- `Σ x_i⁴`. -/
def X4L : List TrmN := [(1, 0, [(0, 4)])]
/-- `Σ x_i⁶`. -/
def X6L : List TrmN := [(1, 0, [(0, 6)])]

/-- The numerator of `s^{c₁} β₂^{c₂} β₃^{c₃}`. -/
def wordL (c1 c2 c3 : ℕ) : List TrmN := mulL (powL sL33 c1) (mulL (powL N2L c2) (powL N3L c3))

/-- The engine output with the fuel and the degree bound of `(3, 3)`. -/
noncomputable abbrev I33 (p : ℕ → ℝ) (W : ℕ → ℕ → ℝ) (Z0 : ℝ) (L : List TrmN) : ℝ :=
  ILF p W Z0 12 8 4 L

/-- The denominator `(1 + p₄)^{c₂} (1 + 3p₄ + 2p₆)^{c₃}` of `β₂^{c₂} β₃^{c₃}`. -/
noncomputable def den33 (p : ℕ → ℝ) (c2 c3 : ℕ) : ℝ :=
  (1 + p 4) ^ c2 * (1 + 3 * p 4 + 2 * p 6) ^ c3

/-- `E_Q[s^{c₁} β₂^{c₂} β₃^{c₃}]`. -/
noncomputable def mom33F (p : ℕ → ℝ) (W : ℕ → ℕ → ℝ) (Z0 : ℝ) (c1 c2 c3 : ℕ) : ℝ :=
  I33 p W Z0 (wordL c1 c2 c3) / den33 p c2 c3

/-- `E_Q[τ s^{c₁} β₂^{c₂} β₃^{c₃}]`, with
`τ = 5/3 + Σx⁴ + Σx⁶/3 − s² − N₂²/(2(1+p₄)) − N₃²/(6(1+3p₄+2p₆))`. -/
noncomputable def tau33F (p : ℕ → ℝ) (W : ℕ → ℕ → ℝ) (Z0 : ℝ) (c1 c2 c3 : ℕ) : ℝ :=
  (5 / 3 * I33 p W Z0 (wordL c1 c2 c3) + I33 p W Z0 (mulL X4L (wordL c1 c2 c3)) +
    I33 p W Z0 (mulL X6L (wordL c1 c2 c3)) / 3 -
    I33 p W Z0 (mulL (powL sL33 2) (wordL c1 c2 c3)) -
    I33 p W Z0 (mulL (powL N2L 2) (wordL c1 c2 c3)) / (2 * (1 + p 4)) -
    I33 p W Z0 (mulL (powL N3L 2) (wordL c1 c2 c3)) / (6 * (1 + 3 * p 4 + 2 * p 6))) /
      den33 p c2 c3

/-- The weights at `(3, 3)` as a function of `p`, `W`, `Z0` and `n`: for `l = 0`,
`E Π_r β_{j_r}`; for `l = 1`, `wickC(i,1) σ² E[τ Π_r β_{j_r}]` (`wickC(2,1) = 1`,
`wickC(3,1) = 3`, `σ² = 6/(n(n+1)(n+2)(n+3))`); `0` at the keys `l ≥ 2`, which `pg` does not
read. -/
noncomputable def w33F (p : ℕ → ℝ) (W : ℕ → ℕ → ℝ) (Z0 nn : ℝ) (κ : KeyRK 3 3) : ℝ :=
  if (κ.1.2 : ℕ) = 0 then mom33F p W Z0 (cnt69 κ 1) (cnt69 κ 2) (cnt69 κ 3)
  else if (κ.1.2 : ℕ) = 1 then
    (if (κ.1.1 : ℕ) = 2 then 1 else 3) * (1 / (nn * (nn + 1) * (nn + 2) * (nn + 3) / 6)) *
      tau33F p W Z0 (cnt69 κ 1) (cnt69 κ 2) (cnt69 κ 3)
  else 0

/-- The weights at `(3, 3)` at `(t, v)`. -/
noncomputable def w33 (n K : ℕ) (t : ℝ) (v : Fin n → ℝ) (κ : KeyRK 3 3) : ℝ :=
  w33F (pw v) (W74 n K t) (Z69 n K t 0) n κ

/-! ## The inputs of the constant-size stage at `(3, 3)` -/

/-- The index of the inputs of the constant-size stage: the power sums `p_e`, `e ≤ 16`; the table
sums `W_{c,q}`, `c ≤ q ≤ 4`; `Z_0`. -/
abbrev V33 := Fin 17 ⊕ (Fin 5 × Fin 5) ⊕ Unit

/-- The inputs of the constant-size stage at `(t, v)`. -/
noncomputable def inp33 (n K : ℕ) (t : ℝ) (v : Fin n → ℝ) : V33 → ℝ :=
  Sum.elim (fun e => pw v e)
    (Sum.elim (fun cq => if (cq.1 : ℕ) ≤ (cq.2 : ℕ) then W74 n K t cq.1 cq.2 else 0)
      (fun _ => Z69 n K t 0))

/-- The power sums read from an input vector (`0` out of range). -/
def pOf (y : V33 → ℝ) (a : ℕ) : ℝ := if h : a < 17 then y (Sum.inl ⟨a, h⟩) else 0

/-- The table sums read from an input vector (`0` out of range). -/
def WOf (y : V33 → ℝ) (c q : ℕ) : ℝ :=
  if h : c < 5 ∧ q < 5 then y (Sum.inr (Sum.inl (⟨c, h.1⟩, ⟨q, h.2⟩))) else 0

/-- The weights at `(3, 3)` from an input vector (`n = p_0`). -/
noncomputable def w33Y (y : V33 → ℝ) (κ : KeyRK 3 3) : ℝ :=
  w33F (pOf y) (WOf y) (y (Sum.inr (Sum.inr ()))) (y (Sum.inl 0)) κ

end BstLean.Part74
