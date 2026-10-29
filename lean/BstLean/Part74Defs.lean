import BstLean.Part69Defs
import BstLean.Part43Floor
import BstLean.Part56MC_GaussianDensity
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Part 74, wave 0: definitions for the generic moment engine

Role: `delegations/statements/p74-spec.md`. Source: `delegations/answers/omSU2-opus-prover.md`
(Theorem S′ and Lemma G3, the Stein route).

* `pw v e = Σ_i v_i^e` (power sums), `W74 n K t c q = Σ_{j ≤ K} (t^j/j!) U_j j^{\underline c} /
  Π_{i<q} (n + 2j + 2i)` (the table sums of the Stein basis).
* `Sp v a b = Σ_i v_i^a X_i^b` as a polynomial, `monP v M = Π_{(a,b) ∈ M} Sp v a b`.
* `gE`: the standard Gaussian expectation of a polynomial, with the Stein identity `gE_X_mul`.
* `dvD v = Σ_i v_i ∂_i` as a derivation.
* The computable evaluators `EG` (Lemma G3), `EGs` and `dvEs` (`gE ∘ ∂_v^c` on `γ^e Π S_{a,b}`),
  generic in a commutative ring.
-/

namespace BstLean.Part74

open MeasureTheory MvPolynomial
open BstLean.Part29 (stdGauss)
open BstLean.Part69 (U69 Z69)

variable {n : ℕ}

/-- The power sum `p_e(v) = Σ_i v_i^e`. -/
noncomputable def pw (v : Fin n → ℝ) (e : ℕ) : ℝ := ∑ i, v i ^ e

/-- `W_{c,q} = Σ_{j ≤ K} (t^j/j!) U_j j(j−1)⋯(j−c+1) / Π_{i<q} (n + 2j + 2i)`. -/
noncomputable def W74 (n K : ℕ) (t : ℝ) (c q : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1), t ^ j / (j.factorial : ℝ) * U69 n j * (j.descFactorial c : ℝ) /
    ∏ i ∈ Finset.range q, ((n : ℝ) + 2 * (j : ℝ) + 2 * (i : ℝ))

/-- `S_{a,b} = Σ_i v_i^a X_i^b`. -/
noncomputable def Sp (v : Fin n → ℝ) (a b : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, C (v i ^ a) * X i ^ b

/-- A monomial in the `S_{a,b}`: a list of pairs `(a, b)`. -/
abbrev Mon := List (ℕ × ℕ)

/-- The `x`-degree of a monomial. -/
def mdeg (M : Mon) : ℕ := (M.map Prod.snd).sum

/-- The polynomial `Π_{(a,b) ∈ M} S_{a,b}`. -/
noncomputable def monP (v : Fin n → ℝ) (M : Mon) : MvPolynomial (Fin n) ℝ :=
  (M.map fun ab => Sp v ab.1 ab.2).prod

/-- The directional derivative `∂_v = Σ_i v_i ∂_i`. -/
noncomputable def dvD (v : Fin n → ℝ) :
    Derivation ℝ (MvPolynomial (Fin n) ℝ) (MvPolynomial (Fin n) ℝ) :=
  ∑ i, v i • pderiv i

elab "steinImported74" : term => do
  let env ← Lean.getEnv
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
    name.toString == "_private.BstLean.Part43Floor.0.BstLean.Part43.gaussian_polynomial_stein")
    | throwError "Part43Floor.gaussian_polynomial_stein is unavailable"
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

theorem gauss_integrable74 (P : MvPolynomial (Fin n) ℝ) :
    Integrable (fun z => eval z P) (stdGauss (Fin n)) :=
  (BstLean.Part56.mc56_polynomial_memLp P).integrable (by simp)

/-- The standard Gaussian expectation of a polynomial. -/
noncomputable def gE : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ where
  toFun P := ∫ z, eval z P ∂stdGauss (Fin n)
  map_add' P Q := by
    simp only [eval_add]
    exact integral_add (gauss_integrable74 P) (gauss_integrable74 Q)
  map_smul' c P := by
    simp only [smul_eq_C_mul, eval_mul, eval_C, smul_eq_mul]
    exact integral_const_mul _ _

theorem gE_apply (P : MvPolynomial (Fin n) ℝ) : gE P = ∫ z, eval z P ∂stdGauss (Fin n) := rfl

/-- The Stein identity `E[g_i P(g)] = E[∂_i P(g)]`. -/
theorem gE_X_mul (i : Fin n) (P : MvPolynomial (Fin n) ℝ) :
    gE (X i * P) = gE (pderiv i P) := by
  simpa only [gE, LinearMap.coe_mk, AddHom.coe_mk, eval_mul, eval_X] using
    steinImported74 P i

/-! ## The computable evaluators -/

/-- Pair a head factor `(a, b+1)` with each non-constant factor `(a', b'+1)` of `M`: the pair is
replaced by `(a + a', b + b')` with the coefficient `b' + 1`. -/
def pstep (a b : ℕ) : Mon → List (ℕ × Mon)
  | [] => []
  | (a', 0) :: xs => (pstep a b xs).map (fun y => (y.1, (a', 0) :: y.2))
  | (a', b' + 1) :: xs =>
      (b' + 1, (a + a', b + b') :: xs) :: (pstep a b xs).map (fun y => (y.1, (a', b' + 1) :: y.2))

/-- `∂_v` of a monomial: each non-constant factor `(a, b+1)` becomes `(a+1, b)` with the
coefficient `b + 1`. -/
def dstep : Mon → List (ℕ × Mon)
  | [] => []
  | (a, 0) :: xs => (dstep xs).map (fun y => (y.1, (a, 0) :: y.2))
  | (a, b + 1) :: xs =>
      (b + 1, (a + 1, b) :: xs) :: (dstep xs).map (fun y => (y.1, (a, b + 1) :: y.2))

section Eval

variable {R : Type} [CommRing R]

/-- Lemma G3 as a program: `EG p f M = E_g[Π_{(a,b) ∈ M} S_{a,b}(g)]` for `p = pw v`, given fuel
`f ≥ length M + mdeg M`. -/
def EG (p : ℕ → R) : ℕ → Mon → R
  | _, [] => 1
  | 0, _ :: _ => 0
  | f + 1, (a, 0) :: M => p a * EG p f M
  | f + 1, (a, 1) :: M => ((pstep a 0 M).map fun y => (y.1 : R) * EG p f y.2).sum
  | f + 1, (a, b + 2) :: M =>
      ((b + 1 : ℕ) : R) * EG p f ((a, b) :: M) +
        ((pstep a (b + 1) M).map fun y => (y.1 : R) * EG p f y.2).sum

/-- `EGs p f g e M = E_g[γ^e Π_{(a,b) ∈ M} S_{a,b}(g)]`, `γ = S_{1,1}`, given fuel
`f ≥ length M + mdeg M` and `g ≥ e + mdeg M`. -/
def EGs (p : ℕ → R) (f : ℕ) : ℕ → ℕ → Mon → R
  | _, 0, M => EG p f M
  | 0, _ + 1, _ => 0
  | g + 1, 1, M => ((dstep M).map fun y => (y.1 : R) * EGs p f g 0 y.2).sum
  | g + 1, e + 2, M =>
      ((e + 1 : ℕ) : R) * p 2 * EGs p f g e M +
        ((dstep M).map fun y => (y.1 : R) * EGs p f g (e + 1) y.2).sum

/-- `dvEs p f g c e M = E_g[∂_v^c (γ^e Π_{(a,b) ∈ M} S_{a,b})(g)]`. -/
def dvEs (p : ℕ → R) (f g : ℕ) : ℕ → ℕ → Mon → R
  | 0, e, M => EGs p f g e M
  | c + 1, 0, M => ((dstep M).map fun y => (y.1 : R) * dvEs p f g c 0 y.2).sum
  | c + 1, e + 1, M =>
      ((e + 1 : ℕ) : R) * p 2 * dvEs p f g c e M +
        ((dstep M).map fun y => (y.1 : R) * dvEs p f g c (e + 1) y.2).sum

end Eval

/-! ## The two-point outputs at `(d_M, d_f) = (2, 4)` -/

/-- `E_Q Σ x_i⁴` in the Stein basis. -/
noncomputable def ET74 (n K : ℕ) (t : ℝ) (v : Fin n → ℝ) : ℝ :=
  (3 * (n : ℝ) * W74 n K t 0 2 + 12 * W74 n K t 1 2 + 4 * pw v 4 * W74 n K t 2 2) / Z69 n K t 0

/-- `E_Q (Σ x_i⁴)²` in the Stein basis. -/
noncomputable def ET2_74 (n K : ℕ) (t : ℝ) (v : Fin n → ℝ) : ℝ :=
  (3 * (n : ℝ) * (3 * (n : ℝ) + 32) * W74 n K t 0 4 + 24 * (3 * (n : ℝ) + 32) * W74 n K t 1 4 +
    24 * ((n : ℝ) * pw v 4 + 28 * pw v 4 + 6) * W74 n K t 2 4 +
    32 * (3 * pw v 4 + 4 * pw v 6) * W74 n K t 3 4 + 16 * pw v 4 ^ 2 * W74 n K t 4 4) /
      Z69 n K t 0

/-- `c(r) = 3/2 − r² − r⁴ (1 + q)/2`, so that `κ_x − K̂(r) = c(r) + (Σ x_i⁴)/2` on the sphere. -/
noncomputable def cK74 (q r : ℝ) : ℝ := 3 / 2 - r ^ 2 - r ^ 4 * (1 + q) / 2

/-- The output vector at `(d, k) = (2, 4)`: the node `r`, then `m₀, m₁, m₂`. -/
noncomputable def out74 (r q eT eT2 : ℝ) : Unit ⊕ Fin 3 → ℝ :=
  Sum.elim (fun _ => r)
    ![1, cK74 q r + eT / 2, cK74 q r ^ 2 + cK74 q r * eT + eT2 / 4]

end BstLean.Part74
