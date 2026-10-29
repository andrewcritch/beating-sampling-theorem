import BstLean.Part176T171
import BstLean.Part176Stat
import BstLean.Part176Num

/-!
# Part 176 (file `End`): the unconditional classifier theorem for every `n ≥ 45 000`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_45000`**: Part 172's `classifier_paper_uncond` for every `n` with
  `45 000 ≤ n ≤ 10²⁰`: the free-threshold route `N45.classifier_paper_gen45k` (file `T171`) at the
  thresholds `S_m = 1/(5n)`, `D_m = 16/n³`, `V_m = 64/n⁴`, `P_m = 2/n⁴`, with the numerics
  `N45.numF45`, `N45.numW45` (file `Num`) and the statistics charge `N45.stat_charge45` (file `Stat`).
* **`classifier_paper_uncond_nocap45`** (headline): the same for every `n ≥ 45 000`, with NO upper
  end; for `n ≥ 10²⁰` it uses Part 174's `Cap.classifier_paper_uncond_large` (`n ≥ 10¹⁹`).
* `uncond_nocap45_eq_172`, `uncond_nocap45_eq_175`: on the common ranges the proof terms are equal
  by `rfl`; so the conclusion is exactly the proposition of Part 172 (and of Part 175).
-/

namespace BstLean.Part176

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171

/-- **The classifier theorem with no hypothesis, for every `n` with `45 000 ≤ n ≤ 10²⁰` and every
threshold `t`**: the paper's program (Lean's exact-moment form `paperDesignP`) succeeds,
`p ≤ U ≤ max(10p, 1/100)`, with probability at least `99/100` over the actual random networks
`(W, A, F)` and the program's draws. -/
theorem classifier_paper_uncond_45000 {n : ℕ} (hn : 45000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  obtain ⟨hF0, hF1, hF2, hF⟩ := N45.numF45 hn
  obtain ⟨hW0, hW1, hW2, hW⟩ := N45.numW45 hn
  exact N45.classifier_paper_gen45k hn t (Sm := SminN n) (Dm := DmN n) (Vm := VmN n)
    (Pm := 2 * PmN n) (z₁ := 211 / 100) (z₂ := 754 / 100) (by unfold SminN; positivity)
    (by norm_num) (by norm_num) z1_pow z2_pow hF0 hF1 hF2 hF hW0 hW1 hW2 hW
    (fun _ hw => N45.stat_charge45 hn hN hw)

/-- **The classifier theorem with no hypothesis, for every `n ≥ 45 000` (no upper end) and every
threshold `t`** (Part 176's headline): the paper's program (Lean's exact-moment form
`paperDesignP`) succeeds, `p ≤ U ≤ max(10p, 1/100)`, with probability at least `99/100` over the
actual random networks `(W, A, F)` and the program's draws. -/
theorem classifier_paper_uncond_nocap45 {n : ℕ} (hn : 45000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  rcases le_total (n : ℝ) (10 ^ 20) with h | h
  · exact classifier_paper_uncond_45000 hn h t
  · exact BstLean.Part174.Cap.classifier_paper_uncond_large (le_trans (by norm_num) h) t

/-- The conclusion is Part 172's (proofs equal by `rfl` on `80 000 ≤ n ≤ 10²⁰`). -/
theorem uncond_nocap45_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_nocap45 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

/-- The conclusion is Part 175's (proofs equal by `rfl` on `49 000 ≤ n`). -/
theorem uncond_nocap45_eq_175 {n : ℕ} (hn : 49000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_nocap45 (by omega) t =
      BstLean.Part175.classifier_paper_uncond_nocap49 hn t :=
  rfl

end BstLean.Part176
