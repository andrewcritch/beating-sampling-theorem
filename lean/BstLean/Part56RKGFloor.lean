import BstLean.Part56Defs
import BstLean.Part56RKGFloor_Variance
import BstLean.Part56RKGFloor_Balance

/-!
# Part 56, wave 1: Theorem RK-G, floor part

Specification: `delegations/answers/p56-spec-opus.md` §3 (`Part56RKGFloor`).
This file imports the frozen definitions and its floor helpers. The floor helpers reuse the finished
Gaussian helpers of `Part56Orth`, as authorized for the resumed proof. The three interface statements
remain hypotheses. Do not use `native_decide` or `axiom` anywhere. Do not edit the statement below.

Proof route (`omRK-opus-prover.md` §4, step 2, with the exact identity of `chRK-codex.md` §3):
for fixed `U`, `E_R Var_μ F = E_x Var_R F(x) − Var_R B + Var_μ a(x)` with `a(x) = E_R F(x)`;
the last term is `≥ 0`; `E_U Var_R B = E(B − g)²` (orthogonality); use the error part.
-/

namespace BstLean.Part56

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono frob Tens TSymm Pn NN baseline heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (LemmaR53 GaussPolar53)
open BstLean.Part48 (SBLevel)

/-- The floor for a constant polynomial, including all coefficient dimensions. -/
private theorem propRKGFloor56_zero (d : ℕ) : PropRKGFloor56 d 0 := by
  intro n μ hμ v hv f0 T hT
  let := hμ.prob
  simp [Sfl, cvarG, BstLean.Part41.fval, EV56, varFQ, BstLean.Part41.varU]

/-- **Theorem RK-G, floor part**, from the error part, orthogonality and the Gaussian split. -/
theorem propRKGFloor56_of (d k : ℕ) (hE : PropRKGErr56 d k) (hO : PropOrth56 d k)
    (hS : PropSplit56 d) : PropRKGFloor56 d k := by
  by_cases hk : k = 0
  · subst k
    exact propRKGFloor56_zero d
  intro n μ hμ v hv f0 T hT
  have he := (hE n μ hμ v hv f0 T hT).2
  have hbalance := FloorAux.integrated_balance k hE hO hS hμ f0 T hT v hv
  nlinarith

end BstLean.Part56
