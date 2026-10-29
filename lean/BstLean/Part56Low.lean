import BstLean.Part56Defs
import BstLean.Part56Low_Kernel
import BstLean.Part56Low_Heat
import BstLean.Part56Low_Assemble
import BstLean.Part56Low_Moment

/-!
# Part 56, wave 1: the lower bound on `S` (Hermite identity, inverse heat operator, lower tail)

Specification: `delegations/answers/p56-spec-opus.md` §3 (`Part56Low`).
The proof uses its own helper files and the completed Part 56 helpers authorized for the resumed
proof. Do not use `native_decide` or `axiom` anywhere. Do not edit the statement below.

Proof route (`omRK-opus-prover.md` §6, T2′ lower bound, checked in `chRK-codex.md` §4): given `U`,
`Var_R h(μ + R) = Σ_{c≥1} (a^c/c!) ‖E ∇^c h(μ+R)‖²`; Jensen in `μ` gives
`E_U Var(F(x)|U) ≥ Σ_c (τ_x^c/c!) ‖Γ_c(κ_x)‖²`, `κ_x = K(x,x) ∈ [1, d+1]`; the inverse heat operator
`T̂_j = (1/j!) Σ_i ((−κ/2)^i/i!) tr^i Γ_{j+2i}(κ)` and Lemma Tr give
`Σ_{j≥1} ‖T̂_j‖² ≤ c n^{⌊(k−1)/2⌋} Σ_c ‖Γ_c(κ)‖²`; `τ_x ≥ ϱ_x² = 1 − (v·x)²`; the lower tail
`E_D ϱ^{2k} ≥ θ^k/2`, `θ = ½ min(1, (n−3)/(2t₊))`, for `t ≤ C n`, `n ≥ 100`.
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

/-- **Lower bound on `S`.** -/
theorem propLow56 (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (C : ℝ) :
    ∃ (cL : ℝ) (n0 : ℕ), 0 < cL ∧ PropLow56 d k C cL n0 := by
  obtain ⟨a, n0, ha, hn0, hAngular⟩ := LowMoment.angular_moment_uniform k C
  obtain ⟨cL, hcL, hLow⟩ := LowAssemble.propLow56_of_angular d k hk hkd C a ha n0 hn0 hAngular
  exact ⟨cL, n0, hcL, hLow⟩


end BstLean.Part56
