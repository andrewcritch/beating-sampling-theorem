import BstLean.Part59Defs
import BstLean.Part59LemmaQ_Bridge

/-!
# Part 59, wave 1: Lemma Q: smoothing acts coordinatewise

Specification: `delegations/answers/p59-spec-opus.md` §3.4. Source: `omDL2-opus-prover.md` §2, Lemma Q.

Suggested route.
* Both sides are polynomials in `a`; it is enough to prove the identity for `a ≥ 0` (or prove the
  coefficient identity directly).
* Part 53's `heatA k a (TF k f0 T)` is the coefficient family of `P_a f = Σ_l (a/2)^l Δ^l f / l!`
  for symmetric `T` (`Δ T[y^{⊗j}] = j(j−1)(tr T)[y^{⊗(j−2)}]`). On a monomial,
  `P_a y^α = Π_i P_a^{(i)} y_i^{α_i}` since `Δ = Σ_i ∂_i²` and the `∂_i²` commute, and
  `P_a t^e = Σ_l (a/2)^l e!/(l!(e−2l)!) t^{e−2l} = q_e(t; a)` (the Hermite recursion
  `q_{e+2} = t q_{e+1} + (e+1) a q_e`).
* Alternatively, by Part 53's Lemma W machinery (`Part53Wick_*.lean`): `fvA k (heatA k a A) y =
  E fvA k A (y + √a G)`, and `E Π_i (y_i + √a g_i)^{α_i} = Π_i q_{α_i}(y_i; a)` by independence.
* Use `coefTens`-style grouping of words by multisets, as in `Part59Coef` (prove what you need here;
  do not import `Part59Coef`).

Replace each `sorry` by a proof. Do not edit the statements or `Part59Defs.lean`. Do not use
`native_decide` or `axiom` anywhere. This file imports `Part59Defs` only; a prover may also import
finished files of Parts 29–58, but no other Part 59 wave-1 file. Name private helpers with the suffix
`59x` or make them `private`, so that `Part59Final` does not see a name clash.
-/

namespace BstLean.Part59

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM contr trL frob IsSymmT Tens TSymm fval Pn varU sdU heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (sg c0 aH g0 heatA fvA Ncirc LemmaR53 GaussPolar53)

variable {n d : ℕ}

/-- **Lemma Q.** -/
theorem lemmaQ59 : LemmaQ59 := by
  classical
  intro n d k c M
  unfold g0
  rw [TF_tensOf59x]
  cases n with
  | zero =>
    have ha : aH 0 d = 0 := by
      simp [aH, BstLean.Part36.DD_eq]
    rw [ha, fvA_heat_zero59x, fvA_zero_dim59x, tensOf_zero_block59x]
    letI : Unique (Mono 0 k) :=
      { default := default, uniq := mono_zero_dim59x k }
    simp [g0Q]
  | succ n =>
    letI : Inhabited (Fin (n + 1)) := ⟨0⟩
    exact (heat_coeff_identity59x c (colM M default) (aH (n + 1) d)
      (aH_nonneg59x (n + 1) d)).symm


end BstLean.Part59
