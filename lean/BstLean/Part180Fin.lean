import BstLean.Part180Endb
import BstLean.Part180Fin24

/-!
# Part 180 (file `Fin`): the unconditional classifier theorem for every `n ≥ 23 000`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_nocap23`**: Part 172's conclusion for every `n ≥ 23 000` and every
  `t`, with no hypothesis and no upper end: file `Endb`'s `classifier_paper_uncond_nocap23H` with
  `hq_proved` (Lemma HQ, file `HQS`).
* `uncond_nocap23_eq_172`, `uncond_nocap23_eq_179`, `uncond_nocap23_eq_24`: `rfl` checks (they
  type-check only because the conclusions are the same proposition).
-/

namespace BstLean.Part180

open BstLean.Part130 BstLean.Part157 BstLean.Part169

/-- **The classifier theorem with no hypothesis, for every `n ≥ 23 000` (no upper end) and every
threshold `t`.** -/
theorem classifier_paper_uncond_nocap23 {n : ℕ} (hn : 23000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_uncond_nocap23H hq_proved hn t

theorem uncond_nocap23_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_nocap23 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

theorem uncond_nocap23_eq_179 {n : ℕ} (hn : 25000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_nocap23 (by omega) t =
      BstLean.Part179.classifier_paper_uncond_nocap25 hn t :=
  rfl

theorem uncond_nocap23_eq_24 {n : ℕ} (hn : 24000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_nocap23 (by omega) t = classifier_paper_uncond_nocap24 hn t :=
  rfl

/-- The statement written with Part 130/156/157/169 names only. -/
example {n : ℕ} (hn : 23000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((BstLean.Part130.mlpTriple 2 n).prod (BstLean.Part157.sampMeas (10 ^ 12) n)).real
      {x | BstLean.Part157.successNet x.1 t (BstLean.Part157.progOut
        (BstLean.Part169.paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_uncond_nocap23 hn t

end BstLean.Part180
