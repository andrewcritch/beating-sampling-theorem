import BstLean.Part184KEnd
import BstLean.Part184GUI
import BstLean.Part184BF3
import BstLean.Part184Uncond

/-!
# Part 184 (file `Uncond18`): the classifier theorem with NO hypothesis for every `n ≥ 18 000`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_18000`**: every `n ≥ 18 000`, every threshold `t`, no upper end.
  Ranges: `18 000 ≤ n < 18 500`: the chain `classifier_paper_uncond_18000HJ` (files `K*`) with
  Lemma HQ, the frame junction `FREE18_proved` (files `G*`, TI-lite at `18 000`, room `−0.0012`),
  the energy bound `EnB_proved` and the location bound `EnFB_proved` (files `BF*`);
  `n ≥ 18 500`: `classifier_paper_uncond_18500` (file `Uncond`).
* `uncond_18000_eq_172`, `uncond_18000_eq_183`, `uncond_18000_eq_18500`: the same proposition (`rfl`).
-/

namespace BstLean.Part184

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_18000 {n : ℕ} (hn : 18000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  by_cases h1 : n < 18500
  · exact classifier_paper_uncond_18000HJ (n₁ := 18000)
      ⟨BstLean.Part180.hq_proved, FREE18_proved⟩ EnB_proved EnFB_proved le_rfl hn
      (by exact_mod_cast h1.le) t
  · exact classifier_paper_uncond_18500 (by omega) t

theorem uncond_18000_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_18000 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

theorem uncond_18000_eq_183 {n : ℕ} (hn : 19000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_18000 (by omega) t =
      BstLean.Part183.classifier_paper_uncond_19000 hn t :=
  rfl

theorem uncond_18000_eq_18500 {n : ℕ} (hn : 18500 ≤ n) (t : ℝ) :
    classifier_paper_uncond_18000 (by omega) t = classifier_paper_uncond_18500 hn t :=
  rfl

end BstLean.Part184

#print axioms BstLean.Part184.classifier_paper_uncond_18000
