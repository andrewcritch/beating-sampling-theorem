import BstLean.Part57Defs
import BstLean.Part53T2
import BstLean.Part48SmallBall
import BstLean.Part57Key_Energy

/-!
# Part 57, wave 1: Key Lemma on a rank-`r` subspace

Specification: `delegations/answers/p57-spec-opus.md` §4.9 (`Part57Key`).
This file imports `Part57Defs` (and existing Parts ≤ 56) only; it must not import another Part 57
wave-1 file. Do not use `native_decide` or `axiom` anywhere. Do not edit the statement below.
A prover may split the proof into sub-files `Part57Key_<Sub>.lean` and keep this statement.

Proof route: Gaussian quadratic moments and a split at half the mean projected squared radius
bound normalized linear second moments by `18/(n-r)`. The ordered tensor kernel and covariance
restriction lemmas from Part 56 give the monomial bound, with `CK = 18 * 4^d`.
-/

namespace BstLean.Part57

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono phiM contr trL frob Tens TSymm fval Pn NN baseline heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part48 (SBLevel)
open BstLean.Part53 (TF sg LemmaR53 GaussPolar53)
open BstLean.Part56 (KRK EV56 LemmaMC56 nuRK)

variable {n d r : ℕ}

theorem keyLemma57 (d r : ℕ) (hr : 1 ≤ r) : ∃ CK : ℝ, 0 ≤ CK ∧ KeyLemma57 d r CK := by
  exact ⟨((2 : ℝ) ^ d) ^ 2 * 18, by positivity, KeyProof.key_from_linear d r hr⟩

end BstLean.Part57
