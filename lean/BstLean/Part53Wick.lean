import BstLean.Part53Defs
import BstLean.Part53Wick_Integrability
import BstLean.Part53Wick_Bridge

/-!
# Part 53, wave 1: Lemma W, the chaos identity in the Gaussian proxy (§4 of the source)

Specification: `delegations/answers/p53-spec-opus.md` §3.3.
Replace each `sorry` by a proof. Do not edit the statements. Do not use `native_decide` or `axiom`
anywhere. This file imports `Part53Defs` only (a prover may also import finished Part 29–52 files,
but no other Part 53 wave-1 file).

Statement (`LemmaW53 k`): for symmetric families `A, A'`, `ψ, ψ' ∈ ℝ^N` and `s ∈ ℝ`,
`E_Z[h_A(s Zψ) h_{A'}(s Zψ')] = Σ_c c! s^{2c} ⟨(P_{s²‖ψ‖²}A)_c, (P_{s²‖ψ'‖²}A')_c⟩ ⟨ψ,ψ'⟩^c`.

Suggested route.
* `Y = s Zψ` and `Y' = s Zψ'` are jointly Gaussian on `ℝⁿ × ℝⁿ`: `E Y_a Y_b = s²‖ψ‖² δ_ab`,
  `E Y_a Y'_b = s²⟨ψ,ψ'⟩ δ_ab`. Only this covariance enters.
* Wick expansion: `h_A(Y) = Σ_c :(P_v A)_c[Y^{⊗c}]:` with `v = s²‖ψ‖²` (Wick product = `P_{−v}` of a
  homogeneous polynomial), and `E[:F[Y^{⊗c}]: :G[Y'^{⊗c'}]:] = δ_{cc'} c! ρ^c ⟨F, G⟩` for symmetric
  `F, G`, `ρ = s²⟨ψ,ψ'⟩`.
* Reuse the Hermite machinery of `Part45CondMean_Hermite.lean` (`hermite_level_lower45`),
  `Part47Pair.lean` (`pair_rep`), `Part52Gauss.lean` (`pair_moment`) if present, and `Part36Hermite`.
  An alternative route: both sides are polynomials in `(s, ψ, ψ')`; prove the identity for the
  generating function `h = exp⟨t, y⟩` (Gaussian moment generating function) and compare coefficients.
* Integrability: a polynomial in `Z` is integrable under `stdGauss` (Part 29/42 lemmas).
-/

namespace BstLean.Part53

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT Tens TSymm fval In41 Pn heavyCount)
open BstLean.Part43 (BofQ varFQ)

variable {n d : ℕ}

/-- **Lemma W.** -/
theorem lemmaW53 (k : ℕ) : LemmaW53 k := by
  intro n d s A A' hA hA' ψ ψ'
  exact ⟨wick_product_integrable53 (n := n) (d := d) k s A A' ψ ψ',
    wick_identity53 (n := n) (d := d) k s A A' hA hA' ψ ψ'⟩

end BstLean.Part53
