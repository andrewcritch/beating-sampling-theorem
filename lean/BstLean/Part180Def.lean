import BstLean.Part179All

/-!
# Part 180 (file `Def`): the definitions of the Lemma HQ fluctuation root

No proof is left open; no `native_decide` or `axiom` is used.

Lemma HQ (`delegations/answers/onC52-opus.md`, §1) replaces `H² ≤ χ²` in the mixture root by
`H² ≤ χ²/4 + (3/4)·E(1 − R)₊³`. In Lean the cubic term is bounded by the conditional moments of
`ε = S/S₀ − 1` and of `a_c δ`:
* `cubP n ε₀ λ λ' A D e6 d6`: the integrated cubic price, from `∫ X² ≤ A²`, `∫ Y² ≤ D²`,
  `∫ X⁶ ≤ e6¹²`, `∫ Y⁶ ≤ d6¹²` (`X = E ε²`, `Y = E (a_c δ)²` on each kept latitude);
  `λ, λ' ∈ (0, 1)` are the free weights of two convexity splits.
* `rootEH`: the fluctuation root `√(2(1 + 1/η)B) + √(𝒞/4 + (3/4)·cubP) + √𝒟` (Part 165's
  `rootE` with the middle term changed).
* `rootFLH`: the same in the latitude-moment interface `LatMom` (Part 162's `rootFL`).
-/

namespace BstLean.Part180

open MeasureTheory ProbabilityTheory Real
open BstLean.Part162

/-- **The integrated cubic price of Lemma HQ.** -/
noncomputable def cubP (n ε₀ lam lam' A D e6 d6 : ℝ) : ℝ :=
  ((n * ((1 + 3 * ε₀) / (4 * (1 - ε₀)))) ^ 3 * (A * √A * e6 ^ 3) / lam' ^ 2 +
      (1 / (2 * (1 - ε₀))) ^ 3 * (D * √D * d6 ^ 3) / (1 - lam') ^ 2) / lam ^ 2 +
    (n * A ^ 2 + 2 * A * D) / ((1 - ε₀) ^ 2 * (1 - lam) ^ 2)

/-- The explicit body of the Lemma HQ root, with the fields of the interface as arguments. -/
noncomputable def rootEH (n : ℕ) (wl ws η CA σl Vs Vl VS ts8 ts12 tl8 tl12 tlq tsq βl lam lam' : ℝ) :
    ℝ :=
  √(2 * (1 + η⁻¹) * Bpap wl ws tlq tsq βl (2 * 12)) +
    √(priceC (1 - eps0 ws σl ^ 2)⁻¹ n (√CA * (2 * wl) / σl)
      (eps0 ws σl) (exp ((1 - eps0 ws σl ^ 2)⁻¹ * (n * eps0 ws σl ^ 2 / 2 +
        (√CA * (2 * wl) / σl) ^ 2 * (1 + eps0 ws σl))))
      (cVw ws σl * ((1 - η)⁻¹ * Vs)) (CA / σl ^ 2 * ((1 - η)⁻¹ * Vl))
      (cEw ws σl * ((iotaP η 8 + c2η η + c3η η ws σl) * ts8))
      (√CA / σl * ((iotaP η 8 + c2η η) * tl8))
      (cEw ws σl * ((iotaP η 12 + c2η η + c3η η ws σl) * ts12))
      (√CA / σl * ((iotaP η 12 + c2η η) * tl12)) / 4 +
      3 / 4 * cubP n (eps0 ws σl) lam lam' (cVw ws σl * ((1 - η)⁻¹ * Vs))
        (CA / σl ^ 2 * ((1 - η)⁻¹ * Vl))
        (cEw ws σl * ((iotaP η 12 + c2η η + c3η η ws σl) * ts12))
        (√CA / σl * ((iotaP η 12 + c2η η) * tl12))) +
    √(Dpap n (Bpap wl ws tlq tsq βl (2 * 12)) CA Vl VS η σl)

variable {n : ℕ}

/-- **The Lemma HQ fluctuation root in the latitude-moment interface** (Part 162's `rootFL`
with the middle term `√(𝒞/4 + (3/4)·cubP)`). -/
noncomputable def rootFLH {D : BstLean.Part157.Design n} {c : BstLean.Part157.Ret n} {σl : ℝ} {q : ℕ}
    (wl ws η CA lam lam' : ℝ) (P : LatMom D c σl q) : ℝ :=
  √(2 * (1 + η⁻¹) * Bpap wl ws P.tlq P.tsq P.βlow q) +
    √(priceC (1 - eps0 ws σl ^ 2)⁻¹ n (√CA * (2 * wl) / σl)
      (eps0 ws σl) (exp ((1 - eps0 ws σl ^ 2)⁻¹ * (n * eps0 ws σl ^ 2 / 2 +
        (√CA * (2 * wl) / σl) ^ 2 * (1 + eps0 ws σl))))
      (cVw ws σl * ((1 - η)⁻¹ * P.Vs)) (CA / σl ^ 2 * ((1 - η)⁻¹ * P.Vl))
      (cEw ws σl * ((iotaP η 8 + c2η η + c3η η ws σl) * P.ts8))
      (√CA / σl * ((iotaP η 8 + c2η η) * P.tl8))
      (cEw ws σl * ((iotaP η 12 + c2η η + c3η η ws σl) * P.ts12))
      (√CA / σl * ((iotaP η 12 + c2η η) * P.tl12)) / 4 +
      3 / 4 * cubP n (eps0 ws σl) lam lam' (cVw ws σl * ((1 - η)⁻¹ * P.Vs))
        (CA / σl ^ 2 * ((1 - η)⁻¹ * P.Vl))
        (cEw ws σl * ((iotaP η 12 + c2η η + c3η η ws σl) * P.ts12))
        (√CA / σl * ((iotaP η 12 + c2η η) * P.tl12))) +
    √(Dpap n (Bpap wl ws P.tlq P.tsq P.βlow q) CA P.Vl P.VS η σl)

end BstLean.Part180
