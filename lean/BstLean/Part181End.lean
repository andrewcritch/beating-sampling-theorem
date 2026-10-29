import BstLean.Part181Endc
import BstLean.Part181Comb
import BstLean.Part180All

/-!
# Part 181 (file `End`): the unconditional classifier theorem for every `n ≥ 22 000`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_nocap22`**: Part 172's conclusion for every `n ≥ 22 000` and every
  `t`, with no hypothesis and no upper end. On `22 000 ≤ n ≤ 23 000`: the chain of this part
  (`classifier_paper_uncond_22000H`) with `HQF_stmt` discharged by Lemma HQ (`hq_proved`, Part
  180) and the frame junction `classifier_paper_free22` (file `Comb`). For `n > 23 000`:
  Part 180's `classifier_paper_uncond_nocap23` (which keeps Part 174's cap removal).
* `uncond_nocap22_eq_172`, `uncond_nocap22_eq_180`: `rfl` checks (they type-check only because
  the conclusions are the same proposition).
-/

namespace BstLean.Part181

open BstLean.Part130 BstLean.Part157 BstLean.Part169

/-- `HQF_stmt` holds: Lemma HQ (Part 180) and the frame junction at `22 000` (file `Comb`). -/
theorem hqf_proved : HQF_stmt := ⟨BstLean.Part180.hq_proved, classifier_paper_free22⟩

/-- **The classifier theorem with no hypothesis, for every `n ≥ 22 000` (no upper end) and every
threshold `t`.** -/
theorem classifier_paper_uncond_nocap22 {n : ℕ} (hn : 22000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  rcases lt_or_ge n 23000 with h | h
  · have hR : (n : ℝ) < 23000 := by exact_mod_cast h
    exact classifier_paper_uncond_22000H hqf_proved hn hR.le t
  · exact BstLean.Part180.classifier_paper_uncond_nocap23 h t

theorem uncond_nocap22_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_nocap22 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

theorem uncond_nocap22_eq_180 {n : ℕ} (hn : 23000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_nocap22 (by omega) t =
      BstLean.Part180.classifier_paper_uncond_nocap23 hn t :=
  rfl

/-- The statement written with Part 130/156/157/169 names only. -/
example {n : ℕ} (hn : 22000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((BstLean.Part130.mlpTriple 2 n).prod (BstLean.Part157.sampMeas (10 ^ 12) n)).real
      {x | BstLean.Part157.successNet x.1 t (BstLean.Part157.progOut
        (BstLean.Part169.paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_uncond_nocap22 hn t

end BstLean.Part181
