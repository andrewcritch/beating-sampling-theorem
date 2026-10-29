import BstLean.Part56Defs
import BstLean.Part56Orth_Integrability
import BstLean.Part56Orth_Conditional
import BstLean.Part56Orth_Mean

/-!
# Part 56, wave 1: the heat form is the conditional expectation (orthogonality)

Specification: `delegations/answers/p56-spec-opus.md` §3 (`Part56Orth`).
This file imports `Part56Defs` (and existing Parts ≤ 55) only; it must not import another Part 56
wave-1 file. Do not use `native_decide` or `axiom` anywhere. Do not edit the statement below.

Proof route (`omRK-opus-prover.md` §3): in the proxy `M = σZ`, the anchors `u_j = σ Z φ_j(v)` are
independent across `j` (disjoint blocks), and `m(x) = μ_x + σ R(x)`, with `R(x) = Z (φ(x) − Σ_j β_j(x)
φ_j(v))` independent of the anchors (Gaussian orthogonal projection: `⟨φ(x) − Σ_j β_j φ_j(v), φ_j(v)⟩ = 0`),
and `R(x)` has independent `N(0, τ(x))` coordinates. Hence `E[f(m(x)) | anchors] =
fvA k (heatA k (σ² τ(x)) (TF k f0 T)) μ_x` (Part 53's heat identity, symmetric `TF`). Fubini in `x`.
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

/-- **Orthogonality**, from the Gaussian split. -/
theorem propOrth56 (d k : ℕ) (hS : PropSplit56 d) : PropOrth56 d k := by
  intro n μ hμ v hv f0 T hT
  refine ⟨Orth.B_memLp hμ k f0 T (BstLean.Part53.sg n d),
    Orth.heat_memLp hμ k f0 T v,
    Orth.variance_integrable hμ k f0 T hT (BstLean.Part53.sg n d), ?_⟩
  intro h _ hh
  exact Orth.orthogonal_of_residual_mean hS hμ k f0 T v hv
    (Orth.centered_resampled_mean hμ k f0 T hT v hv) h hh

end BstLean.Part56
