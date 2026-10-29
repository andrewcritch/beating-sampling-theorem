import BstLean.Part181End
import BstLean.Part182Comb

/-!
# Part 182 (file `End`): the end theorem (range unchanged) and its checks

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_182`**: Part 172's conclusion for every `n ≥ 22 000` and every `t`, with
  no hypothesis and no upper end. **The range is the one of Part 181** (`n₀ = 22 000`): this part
  does not lower `n₀`. The proof is Part 181's `classifier_paper_uncond_nocap22` (which keeps the
  cap removal of Part 174).
* `uncond_182_eq_172`, `uncond_182_eq_181`: `rfl` checks (they type-check only because the
  conclusions are the same proposition).
* What this part adds is CONDITIONAL: `classifier_paper_free22T` (file `Comb`) — the frame junction
  with the frame constant `1.82/n` and the extra room `roomT = 0.0025`, given the geometry `GeoT n`
  and the two-input hypothesis `TI_hyp n 0.386 0.638 0.582 10⁻¹⁸` (paper Lemma `t7:p04:ti` with
  Lemma `t7:p04:MS`).
-/

namespace BstLean.Part182

open BstLean.Part130 BstLean.Part157 BstLean.Part169

/-- **The classifier theorem with no hypothesis, for every `n ≥ 22 000` (no upper end) and every
threshold `t`** (the range of Part 181). -/
theorem classifier_paper_uncond_182 {n : ℕ} (hn : 22000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  BstLean.Part181.classifier_paper_uncond_nocap22 hn t

theorem uncond_182_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_182 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

theorem uncond_182_eq_181 {n : ℕ} (hn : 22000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_182 hn t = BstLean.Part181.classifier_paper_uncond_nocap22 hn t :=
  rfl

/-- The statement written with Part 130/156/157/169 names only. -/
example {n : ℕ} (hn : 22000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((BstLean.Part130.mlpTriple 2 n).prod (BstLean.Part157.sampMeas (10 ^ 12) n)).real
      {x | BstLean.Part157.successNet x.1 t (BstLean.Part157.progOut
        (BstLean.Part169.paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_uncond_182 hn t

end BstLean.Part182

open BstLean.Part182 in
#print axioms classifier_paper_uncond_182
