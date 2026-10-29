import BstLean.Part179T171M
import BstLean.Part179StatM
import BstLean.Part179NumM
import BstLean.Part179EndL

/-!
# Part 179 (file `EndM`): the unconditional classifier theorem for every `n ≥ 26 000`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_26000`**: Part 172's `classifier_paper_uncond` for every `n` with
  `26 000 ≤ n ≤ 10¹⁹`: the free-threshold route `N30.N27.N26.classifier_paper_gen26k` (file
  `T171M`; floor `sd = 0.452` and `η = 1/50` in `N30.dP`; Hellinger split `0.00163 + 0.00482`; top
  `TopJM`, `K² ≤ 4.9`) at the thresholds `S_m = 1/(5n)`, `D_m = 16/n³`, `V_m = 64/n⁴`,
  `P_m = 13/n⁴`, with `numF26`, `numW26` (file `NumM`), the statistics charge `stat_charge26`
  (file `StatM`, cap `10¹⁹`) and Part 177's energy event.
* **`classifier_paper_uncond_nocap26`** : the same for every `n ≥ 26 000`, with NO
  upper end; for `26 000 ≤ n < 27 000` it uses `classifier_paper_uncond_26000`, and for
  `n ≥ 27 000` the theorem `classifier_paper_uncond_nocap27` (file `EndL`).
* `uncond_nocap26_eq_172`, `uncond_nocap26_eq_178`, `uncond_nocap26_eq_27`: equalities proved by
  `rfl`; they type-check only because the conclusions are the same proposition.
-/

namespace BstLean.Part179

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_26000 {n : ℕ} (hn : 26000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 19) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  obtain ⟨hF0, hF1, hF2, hF⟩ := N30.N27.N26.numF26 hn
  obtain ⟨hW0, hW1, hW2, hW⟩ := N30.N27.N26.numW26 hn
  exact N30.N27.N26.classifier_paper_gen26k hn t (Sm := SminN n) (Dm := DmN n) (Vm := VmN n)
    (Pm := 13 * PmN n) (z₁ := 211 / 100) (z₂ := 754 / 100) (by unfold SminN; positivity)
    (by norm_num) (by norm_num) z1_pow z2_pow hF0 hF1 hF2 hF
    hW0 hW1 hW2 hW (fun _ hw => N30.N27.N26.stat_charge26 hn hN hw)
    (BstLean.Part160.measurableSet_agentEv (paperDesignP n) (measurableSet_SEn n))
    (SEn_ret_charge (by omega) (N40.hmomN (by omega)) passF passW measurable_passF
      measurable_passW)
    (fun c hc hτ => ⟨(N30.fb_of_SEn (by omega) hc hτ).2, (N30.fb_of_SEn (by omega) hc hτ).1⟩)

/-- **The classifier theorem with no hypothesis, for every `n ≥ 26 000` (no upper end) and every
threshold `t`**. -/
theorem classifier_paper_uncond_nocap26 {n : ℕ} (hn : 26000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  rcases lt_or_ge n 27000 with h | h
  · have hR : (n : ℝ) < 27000 := by exact_mod_cast h
    exact classifier_paper_uncond_26000 hn (by linarith) t
  · exact classifier_paper_uncond_nocap27 h t

theorem uncond_nocap26_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_nocap26 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

theorem uncond_nocap26_eq_178 {n : ℕ} (hn : 34000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_nocap26 (by omega) t =
      BstLean.Part178.classifier_paper_uncond_nocap34 hn t :=
  rfl

theorem uncond_nocap26_eq_30 {n : ℕ} (hn : 30000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_nocap26 (by omega) t = classifier_paper_uncond_nocap30 hn t :=
  rfl

theorem uncond_nocap26_eq_27 {n : ℕ} (hn : 27000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_nocap26 (by omega) t = classifier_paper_uncond_nocap27 hn t :=
  rfl

end BstLean.Part179
