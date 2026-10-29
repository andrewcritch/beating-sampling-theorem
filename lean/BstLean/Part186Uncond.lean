import BstLean.Part186LEnd
import BstLean.Part186GCombC
import BstLean.Part186Uncond165

/-!
# Part 186 (file `Uncond`): the classifier theorem with NO hypothesis for every `n ≥ 16 384`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_16384`**: every `n ≥ 16 384 = 2¹⁴`, every threshold `t`, no upper end.
  Ranges: `16 384 ≤ n ≤ 16 500`: the chain `classifier_paper_uncond_16384HB` (files `L*`, room
  `−0.002518`) with Lemma HQ, the two-level-core frame junction `FREE16384c_proved` (files `G*`,
  `TC`, `CovC`, `GeoP`; room `−0.002483`, weakened by `FREEg_mono`), `EnB_proved`, `EnFB_proved`
  and `BiasRA80_proved`; `n > 16 500`: `classifier_paper_uncond_16500` (file `Uncond165`).
* `uncond_16384_eq_172`, `uncond_16384_eq_185`, `uncond_16384_eq_16500`: the same proposition (`rfl`).
-/

namespace BstLean.Part186

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_16384 {n : ℕ} (hn : 16384 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  by_cases h1 : n ≤ 16500
  · exact classifier_paper_uncond_16384HB ⟨BstLean.Part180.hq_proved,
      BstLean.Part183.FREEg_mono le_rfl (by norm_num) FREE16384c_proved⟩
      BstLean.Part184.EnB_proved BstLean.Part184.EnFB_proved biasRA80_K hn h1 t
  · exact classifier_paper_uncond_16500 (by omega) t

theorem uncond_16384_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_16384 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

theorem uncond_16384_eq_185 {n : ℕ} (hn : 17000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_16384 (by omega) t = BstLean.Part185.classifier_paper_uncond_17000 hn t :=
  rfl

theorem uncond_16384_eq_16500 {n : ℕ} (hn : 16500 ≤ n) (t : ℝ) :
    classifier_paper_uncond_16384 (by omega) t = classifier_paper_uncond_16500 hn t :=
  rfl

end BstLean.Part186

#print axioms BstLean.Part186.classifier_paper_uncond_16384
#print axioms BstLean.Part186.uncond_16384_eq_172
