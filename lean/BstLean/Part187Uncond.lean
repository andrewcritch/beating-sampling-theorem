import BstLean.Part187MEnd
import BstLean.Part187CmbK16
import BstLean.Part186Uncond

/-!
# Part 187 (file `Uncond`): the classifier theorem with NO hypothesis for every `n ≥ 16 250`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_16250`**: every `n ≥ 16 250`, every threshold `t`, no upper end.
  Ranges: `16 250 ≤ n ≤ 16 384`: the chain `classifier_paper_uncond_16250HB` (files `M*`, room
  `−0.002212`) with Lemma HQ, the frame junction `FREE16250K_proved` (sharp centre energy, file `Kap16`;
  frame `1.975/n`), `EnB_proved`, `EnFB_proved` and Lemma RA at `P_m = 81/n⁴` (`BiasRA81_16250`);
  `n > 16 384`: Part 186's `classifier_paper_uncond_16384`.
* `uncond_16250_eq_172`, `uncond_16250_eq_186`: the same proposition (`rfl`).
-/

namespace BstLean.Part187

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_16250 {n : ℕ} (hn : 16250 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  by_cases h1 : n < 16384
  · exact BstLean.Part187.classifier_paper_uncond_16250HB ⟨BstLean.Part180.hq_proved, FREE16250K_proved⟩
      BstLean.Part184.EnB_proved BstLean.Part184.EnFB_proved BstLean.Part187.M.BiasRA81_proved hn (by omega) t
  · exact BstLean.Part186.classifier_paper_uncond_16384 (by omega) t

theorem uncond_16250_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_16250 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

theorem uncond_16250_eq_186 {n : ℕ} (hn : 16384 ≤ n) (t : ℝ) :
    classifier_paper_uncond_16250 (by omega) t = BstLean.Part186.classifier_paper_uncond_16384 hn t :=
  rfl

end BstLean.Part187

#print axioms BstLean.Part187.classifier_paper_uncond_16250
#print axioms BstLean.Part187.uncond_16250_eq_172
#print axioms BstLean.Part187.uncond_16250_eq_186
