import BstLean.Part174T172
import BstLean.Part174U55T172

/-!
# Part 174 (file `End`): the unconditional classifier theorem for `55 000 ≤ n ≤ 10²⁰`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_57000`**: Part 172's `classifier_paper_uncond` (and Part 173's
  `classifier_paper_uncond_59000`) for every `n` with `57 000 ≤ n ≤ 10²⁰`. The new ingredient is
  the energy fluctuation without the factor `√3` (`exWn_mom_r`, file `Wfl`); the rest is the
  59 000 chain of Part 173 re-proved at 57 000 with retuned constants (files `Root`, `T166`–`T172`).
* **`classifier_paper_uncond_55000`**: the same for every `55 000 ≤ n ≤ 10²⁰`; the 57 000 chain
  re-proved at 55 000 (files `U55Root`, `U55T166`–`U55T172`), with the floor mass bound of file
  `Mass` (`s0P = 0.5097` in place of Part 165's `s0 = 0.5087`).
* `uncond_55000_eq_172`, `uncond_55000_eq_173`, `uncond_57000_eq_172`, `uncond_57000_eq_173`: on the common range, the proof terms are equal by
  `rfl`; so the conclusion is exactly that of Part 172 (and of Part 173).
-/

namespace BstLean.Part174

open BstLean.Part130 BstLean.Part157 BstLean.Part169

/-- **The classifier theorem with no hypothesis, for every `n` with `57 000 ≤ n ≤ 10²⁰` and every
threshold `t`**: the paper's program (Lean's exact-moment form `paperDesignP`) succeeds,
`p ≤ U ≤ max(10p, 1/100)`, with probability at least `99/100` over the actual random networks
`(W, A, F)` and the program's draws. Part 173 had `59 000 ≤ n`; Part 172 had `80 000 ≤ n`. -/
theorem classifier_paper_uncond_57000 {n : ℕ} (hn : 57000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  N57.classifier_paper_uncond57k hn hN t

/-- The conclusion is Part 172's: on `80 000 ≤ n` the two proofs are equal by `rfl` (so the two
propositions are definitionally equal). -/
theorem uncond_57000_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_57000 (by omega) hN t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

/-- The conclusion is Part 173's: on `59 000 ≤ n` the two proofs are equal by `rfl`. -/
theorem uncond_57000_eq_173 {n : ℕ} (hn : 59000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_57000 (by omega) hN t =
      BstLean.Part173.classifier_paper_uncond_59000 hn hN t :=
  rfl

/-- **The classifier theorem with no hypothesis, for every `n` with `55 000 ≤ n ≤ 10²⁰` and every
threshold `t`** (Part 174's headline): the paper's program (Lean's exact-moment form
`paperDesignP`) succeeds, `p ≤ U ≤ max(10p, 1/100)`, with probability at least `99/100` over the
actual random networks `(W, A, F)` and the program's draws. -/
theorem classifier_paper_uncond_55000 {n : ℕ} (hn : 55000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  N55.classifier_paper_uncond55k hn hN t

/-- The conclusion is Part 172's (proofs equal by `rfl` on `80 000 ≤ n`). -/
theorem uncond_55000_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_55000 (by omega) hN t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

/-- The conclusion is Part 173's (proofs equal by `rfl` on `59 000 ≤ n`). -/
theorem uncond_55000_eq_173 {n : ℕ} (hn : 59000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_55000 (by omega) hN t =
      BstLean.Part173.classifier_paper_uncond_59000 hn hN t :=
  rfl

end BstLean.Part174
