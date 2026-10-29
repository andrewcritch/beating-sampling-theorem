import BstLean.Part56MC_Endpoints
import BstLean.Part56MC_Final

/-!
# Part 56, wave 1: Lemma MC (maximal correlation of Gaussian pairs)

Specification: `delegations/answers/p56-spec-opus.md` §3 (`Part56MC`).
This file imports `Part56Defs` (and existing Parts ≤ 55) only; it must not import another Part 56
wave-1 file. Do not use `native_decide` or `axiom` anywhere. Do not edit the statement below.

Proof route (`chRK-codex.md` §3): standardize; expand the centred `Φ, Ψ` in the orthonormal
multivariate Hermite basis; `Cov = Σ_{|α|≥1} ρ^{|α|} Φ̂_α Ψ̂_α` (Mehler); `|ρ|^{|α|} ≤ |ρ|` and
Cauchy–Schwarz. Reuse the Hermite machinery of `Part45CondMean_Hermite.lean`, `Part48Hyper.lean`,
`Part53Wick*.lean` where it fits. The cases `|ρ| = 1` follow from Cauchy–Schwarz alone.
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

/-- **Lemma MC.** -/
theorem lemmaMC56 : LemmaMC56 := by
  intro n ρ hρ Φ Ψ hΦ hΨ
  by_cases hn : n = 0
  · subst n
    exact mc56_dim_zero ρ Φ Ψ
  by_cases hz : ρ = 0
  · subst ρ
    exact mc56_zero n Φ Ψ
  by_cases hp : ρ = 1
  · subst ρ
    exact mc56_one n Φ Ψ hΦ hΨ
  by_cases hm : ρ = -1
  · subst ρ
    exact mc56_neg_one n Φ Ψ hΦ hΨ
  have hs : 0 ≤ 1 - ρ ^ 2 := by
    obtain ⟨hl, hu⟩ := abs_le.mp hρ
    nlinarith
  have hab : ρ ^ 2 + Real.sqrt (1 - ρ ^ 2) ^ 2 = 1 := by
    rw [Real.sq_sqrt hs]
    ring
  exact mc56_full ρ (Real.sqrt (1 - ρ ^ 2)) hab hρ Φ Ψ hΦ hΨ

end BstLean.Part56
