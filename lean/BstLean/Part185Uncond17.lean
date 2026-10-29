import BstLean.Part185KEnd
import BstLean.Part185GComb
import BstLean.Part185D7
import BstLean.Part185Uncond1725

/-!
# Part 185 (file `Uncond17`): the classifier theorem with NO hypothesis for every `n ≥ 17 000`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_17000`**: every `n ≥ 17 000`, every threshold `t`, no upper end.
  Ranges: `17 000 ≤ n ≤ 17 250`: the chain `classifier_paper_uncond_17000HB` (files `K*`, removal
  tolerance `η = 1/250`, floor `sd = 0.4482`, room `−0.0016`) with Lemma HQ, the frame junction
  `FREE17g_of_TI` (files `G*`, room `−0.001567`, weakened by `FREEg_mono`) fed by the two-sided
  Lemma TI `TI_two_17000` (files `D*`, `λ = 0.645` on `[0.370, 0.655]`), `EnB_proved`,
  `EnFB_proved`; `n > 17 250`: `classifier_paper_uncond_17250` (file `Uncond1725`).
* `uncond_17000_eq_172`, `uncond_17000_eq_184`, `uncond_17000_eq_17250`: the same proposition (`rfl`).
-/

namespace BstLean.Part185

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

/-- The frame junction at `17 000` with no hypothesis. -/
theorem FREE17_proved : BstLean.Part183.FREEg_stmt 17000 (-(1567 / 1000000)) :=
  BstLean.Part183.F17.FREE17g_of_TI TI_two_17000

theorem classifier_paper_uncond_17000 {n : ℕ} (hn : 17000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  by_cases h1 : n ≤ 17250
  · exact classifier_paper_uncond_17000HB ⟨BstLean.Part180.hq_proved,
      BstLean.Part183.FREEg_mono le_rfl (by norm_num) FREE17_proved⟩
      BstLean.Part184.EnB_proved BstLean.Part184.EnFB_proved hn h1 t
  · exact classifier_paper_uncond_17250 (by omega) t

theorem uncond_17000_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_17000 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

theorem uncond_17000_eq_184 {n : ℕ} (hn : 17500 ≤ n) (t : ℝ) :
    classifier_paper_uncond_17000 (by omega) t = BstLean.Part184.classifier_paper_uncond_17500 hn t :=
  rfl

theorem uncond_17000_eq_17250 {n : ℕ} (hn : 17250 ≤ n) (t : ℝ) :
    classifier_paper_uncond_17000 (by omega) t = classifier_paper_uncond_17250 hn t :=
  rfl

end BstLean.Part185

#print axioms BstLean.Part185.classifier_paper_uncond_17000
