import BstLean.Part186KEnd
import BstLean.Part186FPrv
import BstLean.Part186RA
import BstLean.Part185Uncond17

/-!
# Part 186 (file `Uncond165`): the classifier theorem with NO hypothesis for every `n ≥ 16 500`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_16500`**: every `n ≥ 16 500`, every threshold `t`, no upper end.
  Ranges: `16 500 ≤ n ≤ 17 000`: the chain `classifier_paper_uncond_16500HB` (files `K*`, room
  `−0.002691`) with Lemma HQ, the frame junction `FREE165_proved` (files `F*`), `EnB_proved`,
  `EnFB_proved` and the row-averaged bias moments `BiasRA80_proved` (files `RA*`);
  `n > 17 000`: Part 185's `classifier_paper_uncond_17000` (which keeps Part 174's cap removal).
* `uncond_16500_eq_172`, `uncond_16500_eq_185`: the same proposition (`rfl`).
-/

namespace BstLean.Part186

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem biasRA80_K : BstLean.Part186.K.BiasRA80_stmt := fun hn _ hG => BiasRA80_proved hn hG

theorem classifier_paper_uncond_16500 {n : ℕ} (hn : 16500 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  by_cases h1 : n ≤ 17000
  · exact classifier_paper_uncond_16500HB ⟨BstLean.Part180.hq_proved, FREE165_proved⟩
      BstLean.Part184.EnB_proved BstLean.Part184.EnFB_proved biasRA80_K hn h1 t
  · exact BstLean.Part185.classifier_paper_uncond_17000 (by omega) t

theorem uncond_16500_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_16500 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

theorem uncond_16500_eq_185 {n : ℕ} (hn : 17000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_16500 (by omega) t = BstLean.Part185.classifier_paper_uncond_17000 hn t :=
  rfl

end BstLean.Part186

#print axioms BstLean.Part186.classifier_paper_uncond_16500
