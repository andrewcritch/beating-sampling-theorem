import BstLean.Part74GenDefs

/-!
# Part 74: the weights of the line program at a general degree pair `(d, k)` — definitions

* `AL σ j`: the Newton list of `j! h_j` (`h_j` the complete homogeneous symmetric polynomial), with
  the power sum `π_b` replaced by the factor `S_{σ b}`:
  `A_0 = 1`, `A_{j+1} = Σ_{m ≤ j} j^{\underline m} π_{m+1} A_{j−m}`.
  `sigX b = (b, b)` gives `j! k_j(x, v)`; `sigXX b = (0, 2b)` gives `j! k_j(x, x)`;
  `sigV b = (2b, 0)` gives `j! k_j(v, v)`.
* `wGenF`, `wGen`: the weights `wickC(i,l) σ^{2l} E_Q[τ^l Π_r β_{j_r}]` through the engine output
  `ILF`, with `τ = Σ_{j=1}^d (k_j(x,x) − k_j(x,v)²/k_j(v,v))` expanded over the `2d` terms.
* `VG d k`, `inpG`, `pOfG`, `WOfG`, `wGenY`: the inputs of the constant-size stage.
-/

namespace BstLean.Part74

open BstLean.Part56
open BstLean.Part69 (Z69)

variable {n : ℕ}

/-- One Newton step: from `[A_j, A_{j−1}, …]` (read from position `m`), the list of
`Σ_m j^{\underline m} π_{m+1} A_{j−m}`. -/
def newtStep (σ : ℕ → ℕ × ℕ) (j : ℕ) : ℕ → List (List TrmN) → List TrmN
  | _, [] => []
  | m, Lm :: rest =>
      (Lm.map fun t => (j.descFactorial m * t.1, t.2.1, σ (m + 1) :: t.2.2)) ++
        newtStep σ j (m + 1) rest

/-- `[A_j, A_{j−1}, …, A_0]`. -/
def ALs (σ : ℕ → ℕ × ℕ) : ℕ → List (List TrmN)
  | 0 => [[(1, 0, [])]]
  | j + 1 => newtStep σ j 0 (ALs σ j) :: ALs σ j

/-- The Newton list of `j! h_j`. -/
def AL (σ : ℕ → ℕ × ℕ) (j : ℕ) : List TrmN := (ALs σ j).headD []

/-- `π_b ↦ S_{b,b}`: `k_j(x, v)`. -/
def sigX (b : ℕ) : ℕ × ℕ := (b, b)
/-- `π_b ↦ S_{0,2b}`: `k_j(x, x)`. -/
def sigXX (b : ℕ) : ℕ × ℕ := (0, 2 * b)
/-- `π_b ↦ S_{2b,0} = p_{2b}`: `k_j(v, v)`. -/
def sigV (b : ℕ) : ℕ × ℕ := (2 * b, 0)

/-- Fuel and degree bound at `(d, k)`. -/
def fuelF (d k : ℕ) : ℕ := 2 * d * k + 2
def fuelG (d k : ℕ) : ℕ := d * k
def degD (d k : ℕ) : ℕ := (d * k + 1) / 2

/-- `k_j(v, v)` from the power sums. -/
noncomputable def kvvF (p : ℕ → ℝ) (d k j : ℕ) : ℝ :=
  dvEsL p (fuelF d k) (fuelG d k) 0 (AL sigV j) / (j.factorial : ℝ)

/-- The product of a finite family of polynomials. -/
def prodL {m : ℕ} (Ls : Fin m → List TrmN) : List TrmN :=
  (List.ofFn Ls).foldr mulL [(1, 0, [])]

/-- The `2d` terms of `τ`: the lists. -/
def tauL (d : ℕ) : Fin d ⊕ Fin d → List TrmN
  | Sum.inl j => AL sigXX ((j : ℕ) + 1)
  | Sum.inr j => powL (AL sigX ((j : ℕ) + 1)) 2

/-- The `2d` terms of `τ`: the coefficients `1/j!` and `−1/(j!² k_j(v,v))`. -/
noncomputable def tauC (p : ℕ → ℝ) (d k : ℕ) : Fin d ⊕ Fin d → ℝ
  | Sum.inl j => 1 / (((j : ℕ) + 1).factorial : ℝ)
  | Sum.inr j => -1 / ((((j : ℕ) + 1).factorial : ℝ) ^ 2 * kvvF p d k ((j : ℕ) + 1))

/-- `𝒟 = n C(n+d, d)` as a function of a real `n`. -/
noncomputable def DDF (nn : ℝ) (d : ℕ) : ℝ :=
  nn * (∏ i ∈ Finset.range d, (nn + ((i : ℝ) + 1))) / (d.factorial : ℝ)

/-- The weights of the line program at `(d, k)` as a function of `p`, `W`, `Z0`, `n`. -/
noncomputable def wGenF {k d : ℕ} (p : ℕ → ℝ) (W : ℕ → ℕ → ℝ) (Z0 nn : ℝ) (κ : KeyRK k d) : ℝ :=
  wickC κ.1.1 κ.1.2 * (1 / DDF nn d) ^ (κ.1.2 : ℕ) *
    (∑ μ : Fin (κ.1.2 : ℕ) → Fin d ⊕ Fin d, (∏ a, tauC p d k (μ a)) *
      ILF p W Z0 (fuelF d k) (fuelG d k) (degD d k)
        (mulL (prodL fun a => tauL d (μ a)) (prodL fun r => AL sigX (κ.2 r)))) /
    (∏ r, (((κ.2 r : ℕ).factorial : ℝ) * kvvF p d k (κ.2 r)))

/-- The weights of the line program at `(d, k)` at `(t, v)`. -/
noncomputable def wGen {k d : ℕ} (n K : ℕ) (t : ℝ) (v : Fin n → ℝ) (κ : KeyRK k d) : ℝ :=
  wGenF (pw v) (W74 n K t) (Z69 n K t 0) n κ

/-! ## The inputs of the constant-size stage -/

/-- The index of the inputs: the power sums `p_e`, `e ≤ 2dk + 2`; the table sums `W_{c,q}`,
`c ≤ q ≤ degD d k`; `Z_0`. -/
abbrev VG (d k : ℕ) := Fin (2 * d * k + 3) ⊕ (Fin (degD d k + 1) × Fin (degD d k + 1)) ⊕ Unit

/-- The inputs of the constant-size stage at `(t, v)`. -/
noncomputable def inpG (d k n K : ℕ) (t : ℝ) (v : Fin n → ℝ) : VG d k → ℝ :=
  Sum.elim (fun e => pw v e)
    (Sum.elim (fun cq => if (cq.1 : ℕ) ≤ (cq.2 : ℕ) then W74 n K t cq.1 cq.2 else 0)
      (fun _ => Z69 n K t 0))

/-- The power sums read from an input vector (`0` out of range). -/
def pOfG {d k : ℕ} (y : VG d k → ℝ) (a : ℕ) : ℝ :=
  if h : a < 2 * d * k + 3 then y (Sum.inl ⟨a, h⟩) else 0

/-- The table sums read from an input vector (`0` out of range). -/
def WOfG {d k : ℕ} (y : VG d k → ℝ) (c q : ℕ) : ℝ :=
  if h : c < degD d k + 1 ∧ q < degD d k + 1 then y (Sum.inr (Sum.inl (⟨c, h.1⟩, ⟨q, h.2⟩))) else 0

/-- The weights at `(d, k)` from an input vector (`n = p_0`). -/
noncomputable def wGenY {k d : ℕ} (y : VG d k → ℝ) (κ : KeyRK k d) : ℝ :=
  wGenF (pOfG y) (WOfG y) (y (Sum.inr (Sum.inr ()))) (y (Sum.inl ⟨0, by omega⟩)) κ

end BstLean.Part74
