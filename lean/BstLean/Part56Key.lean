import BstLean.Part56Defs
import BstLean.Part56Key_Energy

/-!
# Part 56, wave 1: the Key Lemma at rank one

Specification: `delegations/answers/p56-spec-opus.md` §3 (`Part56Key`).
This file imports `Part56Defs` (and existing Parts ≤ 55) only; it must not import another Part 56
wave-1 file. Do not use `native_decide` or `axiom` anywhere. Do not edit the statement below.

Proof route: Gaussian second and fourth moments, Part 48's dimension-free fourth moment for the
centered projected squared norm, and a split at half its mean give the normalized linear-functional
second-moment bound. Bivariate coefficient extraction computes the ordered tensor kernel.
An injective enumeration of multisets into ordered tuples bounds the raw covariance energy by the
ordered covariance energy. Cauchy–Schwarz handles different homogeneous degrees and different `s`.
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

/-- **Key Lemma** (rank one). -/
theorem keyLemma56 (d : ℕ) : ∃ CK : ℝ, 0 ≤ CK ∧ KeyLemma56 d CK := by
  obtain ⟨C, hC, hlin⟩ := perpDir_linear_moment56
  refine ⟨((2 : ℝ) ^ d) ^ 2 * C, by positivity, ?_⟩
  exact keyLemma56_from_linear d C hC hlin

end BstLean.Part56
