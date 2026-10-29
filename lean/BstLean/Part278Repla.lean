import BstLean.Part278Good

/-!
# Part 278 (O4, the interface for O5): `REPLA` for the stated design from `REPLA` for
`paperDesignP` at `0.006583`

`repla_st_of_good`: if a chain proves `REPLA_mix_hyp (paperDesignP n) t (6583/10⁶) E` (that is,
without the reserve `10⁻²⁰`), and every `c ∈ E` satisfies the inputs of `odd_root_good`, then
`REPLA_mix_hyp (statedDesign n) t hAL E`. For even `n` the stated design is `paperDesignP n`
(`Part272.statedDesign_even`).
-/

namespace BstLean.Part278

open Real
open BstLean.Part130 (normSq)
open BstLean.Part157 (Ret REPLA_mix_hyp)
open BstLean.Part169 (paperDesignP tauR eR)
open BstLean.Part272 (statedDesign)

variable {n : ℕ}

theorem repla_st_of_good (hn : 16384 ≤ n) (ho : Odd n) (t : ℝ) {E EA : Set (Ret n)}
    (hR : REPLA_mix_hyp (paperDesignP n) t (6583 / 10 ^ 6) E)
    (hgood : ∀ c ∈ E, c ∈ BstLean.Part166.goodD n (paperDesignP n) EA ∧ 0 < tauR c ∧
      46 / 100 ≤ BstLean.Part150.thetaC c.1.2 (tauR c) ∧
      BstLean.Part150.thetaC c.1.2 (tauR c) ≤ 55 / 100 ∧ 0 < eR c ∧
      ∃ χ : ℝ, normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * χ ∧ 0 ≤ χ ∧ χ ≤ n) :
    REPLA_mix_hyp (statedDesign n) t BstLean.Part156.hAL E := by
  have h := repla_transfer (D := paperDesignP n) (D' := statedDesign n) (δ := 1 / 10 ^ 20)
    (fun c => QStand_st t c) hR (fun c hc => by
      obtain ⟨hg, hτ, h0, h1, he, χ, hcA, hχ0, hχ⟩ := hgood c hc
      exact odd_root_good hn ho t c hg hτ h0 h1 he hcA hχ0 hχ)
  unfold BstLean.Part156.hAL
  exact h

theorem repla_st_even (hn : 8 ≤ n) (he : Even n) (t hA : ℝ) {E : Set (Ret n)}
    (hR : REPLA_mix_hyp (paperDesignP n) t hA E) : REPLA_mix_hyp (statedDesign n) t hA E := by
  rw [BstLean.Part272.statedDesign_even hn he]; exact hR

end BstLean.Part278
