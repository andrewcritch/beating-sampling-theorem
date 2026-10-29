import BstLean.Part56LineProg_Construct

/-!
# Part 56, wave 1: the line program and its cost

Specification: `delegations/answers/p56-spec-opus.md` §3 (`Part56LineProg`).
This file imports `Part56Defs` (and existing Parts ≤ 55) only; it must not import another Part 56
wave-1 file. Do not use `native_decide` or `axiom` anywhere. Do not edit the statement below.

Construction (`omRK-opus-prover.md` §3, cost): the monomials `φ_j(v)` (one product each, `≤ N`), the
anchors `u_j = M_j φ_j(v)` (`Σ_j n(2N_j − 1) ≤ 2P`; `u_0` is the constant column, read directly), the
traces `tr^l (TF k f0 T)_i` and the multilinear values `(tr^l A_i)[u_{j_1}, …]` for every key
(`≤ (i+2) n^{i}` each, `≤ (k+1)² (d+1)^k` keys), and the weighted sum. Only the constants `0` and `1`.
Reuse Part 41's `contractProg`, `trProg` and the `Prog` combinators of `CostModel.lean`.
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

/-- **The line program.** -/
theorem lineProg56_exists (n d k : ℕ) (hn : 1 ≤ n) :
    ∃ pg : Prog (In56 n d k) Unit, heavyCount pg = 0 ∧ GSpec56 pg ∧ (pg.cost : ℝ) ≤ costLine56 n d k := by
  exact ⟨lineProg56 n d k, clean_heavyCount lineProg56_clean,
    lineProg56_spec, lineProg56_cost hn⟩


end BstLean.Part56
