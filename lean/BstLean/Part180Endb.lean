import BstLean.Part180T171b
import BstLean.Part180Statb
import BstLean.Part180Numb
import BstLean.Part180End

/-!
# Part 180 (file `Endb`): the classifier theorem for every `n ≥ 23 000`, given Lemma HQ

No proof is left open; no `native_decide` or `axiom` is used.

Every theorem here takes `hHQ : HQ_stmt` (Lemma HQ in the latitude-moment interface, file
`Part180Split`), which the top `BstLean.Part179.N30.N27.N26.N24.N23.classifier_paper_JM23H` uses.

* **`classifier_paper_uncond_23000H`**: Part 172's conclusion for every `n` with
  `23 000 ≤ n ≤ 24 000`: the free-threshold route
  `BstLean.Part179.N30.N27.N26.N25.N24.N23.classifier_paper_gen23k` (files `Part180T167b`–`T171b`;
  bias root `0.00523`, `K² ≤ 5`, room `roomK`) at the thresholds `S_m = 1/(5n)`, `D_m = 16/n³`,
  `V_m = 64/n⁴`, `P_m = 21/n⁴`, with `numF23`, `numW23` (file `Part180Numb`), the statistics
  charge `stat_charge23` (file `Part180Statb`, cap `n ≤ 24 000`, charge `≤ 3·10⁻⁵`) and Part 177's
  energy event.
* **`classifier_paper_uncond_nocap23H`**: the same for every `n ≥ 23 000`, with NO upper end; for
  `n ≥ 24 000` it uses `classifier_paper_uncond_nocap24H` (file `Part180End`).
* `uncond_nocap23H_eq_172`, `uncond_nocap23H_eq_179`: equalities proved by `rfl`; they type-check
  only because the conclusions are the same proposition.
-/

namespace BstLean.Part180

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_23000H (hHQ : HQ_stmt) {n : ℕ} (hn : 23000 ≤ n) (hN : (n : ℝ) ≤ 24000) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  obtain ⟨hF0, hF1, hF2, hF⟩ := BstLean.Part179.N30.N27.N26.N25.N24.N23.numF23 hn
  obtain ⟨hW0, hW1, hW2, hW⟩ := BstLean.Part179.N30.N27.N26.N25.N24.N23.numW23 hn
  exact BstLean.Part179.N30.N27.N26.N25.N24.N23.classifier_paper_gen23k hHQ hn t (Sm := SminN n)
    (Dm := DmN n) (Vm := VmN n)
    (Pm := 21 * PmN n) (z₁ := 211 / 100) (z₂ := 754 / 100) (by unfold SminN; positivity)
    (by norm_num) (by norm_num) z1_pow z2_pow hF0 hF1 hF2 hF
    hW0 hW1 hW2 hW (fun _ hw => BstLean.Part179.N30.N27.N26.N25.N24.N23.stat_charge23 hn hN hw)
    (BstLean.Part160.measurableSet_agentEv (paperDesignP n) (measurableSet_SEn n))
    (SEn_ret_charge (by omega) (N40.hmomN (by omega)) passF passW measurable_passF
      measurable_passW)
    (fun c hc hτ => ⟨(BstLean.Part179.N30.fb_of_SEn (by omega) hc hτ).2,
      (BstLean.Part179.N30.fb_of_SEn (by omega) hc hτ).1⟩)

/-- **The classifier theorem with the one hypothesis `HQ_stmt`, for every `n ≥ 23 000` (no upper end) and every
threshold `t`**. -/
theorem classifier_paper_uncond_nocap23H (hHQ : HQ_stmt) {n : ℕ} (hn : 23000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  rcases lt_or_ge n 24000 with h | h
  · have hR : (n : ℝ) < 24000 := by exact_mod_cast h
    exact classifier_paper_uncond_23000H hHQ hn hR.le t
  · exact classifier_paper_uncond_nocap24H hHQ h t

theorem uncond_nocap23H_eq_172 (hHQ : HQ_stmt) {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20)
    (t : ℝ) :
    classifier_paper_uncond_nocap23H hHQ (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

theorem uncond_nocap23H_eq_179 (hHQ : HQ_stmt) {n : ℕ} (hn : 25000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_nocap23H hHQ (by omega) t =
      BstLean.Part179.classifier_paper_uncond_nocap25 hn t :=
  rfl

end BstLean.Part180
