import BstLean.Part175T172
import BstLean.Part175U49T172

/-!
# Part 175 (file `End`): the unconditional classifier theorem for every `n ≥ 49 000`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_50000`**: Part 172's `classifier_paper_uncond` for every `n` with
  `50 000 ≤ n ≤ 10²⁰` (the 50 000 chain, namespace `N50`).
* **`classifier_paper_uncond_nocap50`**: the same for every `n ≥ 50 000`, with NO upper end; for
  `n ≥ 10²⁰` it uses Part 174's `Cap.classifier_paper_uncond_large` (`n ≥ 10¹⁹`).
* **`classifier_paper_uncond_49000`**, **`classifier_paper_uncond_nocap49`** (headline): the same
  for `49 000 ≤ n ≤ 10²⁰` and for every `n ≥ 49 000` (the 49 000 chain, namespace `N49`, on the
  top of files `M48`, `C48`: Lemma PP at order `P = 400`, `M = 1.0755`).
* `uncond_nocap49_eq_172`, `uncond_nocap49_eq_174`, `uncond_nocap50_eq_172`, `uncond_nocap50_eq_174`: on the common ranges the proof terms are equal
  by `rfl`; so the conclusion is exactly the proposition of Part 172 (and of Part 174).

New ingredients (files `Mass`, `Root`, `Cert`): the World window `θ_in ≤ 0.528` of Part 159 in the
latitude moment `Θ` (certificate charge `21·10⁻⁵`, Part 174: `23·10⁻⁴`) and in the gradient moment
of the floor mass (`0.706 → 0.6306`, with `ε = 0.029` and Lemma PP's `M = 1.125`).
-/

namespace BstLean.Part175

open BstLean.Part130 BstLean.Part157 BstLean.Part169

/-- **The classifier theorem with no hypothesis, for every `n` with `50 000 ≤ n ≤ 10²⁰` and every
threshold `t`**: the paper's program (Lean's exact-moment form `paperDesignP`) succeeds,
`p ≤ U ≤ max(10p, 1/100)`, with probability at least `99/100` over the actual random networks
`(W, A, F)` and the program's draws. -/
theorem classifier_paper_uncond_50000 {n : ℕ} (hn : 50000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  N50.classifier_paper_uncond50k hn hN t

/-- **The classifier theorem with no hypothesis, for every `n ≥ 50 000` (no upper end) and every
threshold `t`** (Part 175's headline). -/
theorem classifier_paper_uncond_nocap50 {n : ℕ} (hn : 50000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  rcases le_total (n : ℝ) (10 ^ 20) with h | h
  · exact classifier_paper_uncond_50000 hn h t
  · exact BstLean.Part174.Cap.classifier_paper_uncond_large (le_trans (by norm_num) h) t

/-- The conclusion is Part 172's: on `80 000 ≤ n ≤ 10²⁰` the two proofs are equal by `rfl`. -/
theorem uncond_nocap50_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_nocap50 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

/-- The conclusion is Part 174's: on `55 000 ≤ n` the two proofs are equal by `rfl`. -/
theorem uncond_nocap50_eq_174 {n : ℕ} (hn : 55000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_nocap50 (by omega) t =
      BstLean.Part174.Cap.classifier_paper_uncond_nocap hn t :=
  rfl

/-- **The classifier theorem with no hypothesis, for every `n` with `49 000 ≤ n ≤ 10²⁰`.** -/
theorem classifier_paper_uncond_49000 {n : ℕ} (hn : 49000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  N49.classifier_paper_uncond49k hn hN t

/-- **The classifier theorem with no hypothesis, for every `n ≥ 49 000` (no upper end) and every
threshold `t`** (Part 175's headline): the paper's program (Lean's exact-moment form
`paperDesignP`) succeeds, `p ≤ U ≤ max(10p, 1/100)`, with probability at least `99/100` over the
actual random networks `(W, A, F)` and the program's draws. -/
theorem classifier_paper_uncond_nocap49 {n : ℕ} (hn : 49000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  rcases le_total (n : ℝ) (10 ^ 20) with h | h
  · exact classifier_paper_uncond_49000 hn h t
  · exact BstLean.Part174.Cap.classifier_paper_uncond_large (le_trans (by norm_num) h) t

/-- The conclusion is Part 172's (proofs equal by `rfl` on `80 000 ≤ n ≤ 10²⁰`). -/
theorem uncond_nocap49_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_nocap49 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

/-- The conclusion is Part 174's (proofs equal by `rfl` on `55 000 ≤ n`). -/
theorem uncond_nocap49_eq_174 {n : ℕ} (hn : 55000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_nocap49 (by omega) t =
      BstLean.Part174.Cap.classifier_paper_uncond_nocap hn t :=
  rfl

end BstLean.Part175
