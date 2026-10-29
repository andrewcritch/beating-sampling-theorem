import BstLean.Part179T171N
import BstLean.Part179StatN
import BstLean.Part179NumN
import BstLean.Part179EndM

/-!
# Part 179 (file `EndN`): the unconditional classifier theorem for every `n ≥ 25 000`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_25000`**: Part 172's `classifier_paper_uncond` for every `n` with
  `25 000 ≤ n ≤ 10¹⁹`: the free-threshold route `N30.N27.N26.N25.classifier_paper_gen25k` (file
  `T171N`; floor `sd = 0.452` and `η = 1/50` in `N30.dP`; Hellinger split `0.00173 + 0.00472`; top
  `TopJN`, `K² ≤ 4.9`, room `roomK = roomC − 10⁻⁴`) at the thresholds `S_m = 1/(5n)`,
  `D_m = 16/n³`, `V_m = 64/n⁴`, `P_m = 15/n⁴`, with `numF25`, `numW25` (file `NumN`), the
  statistics charge `stat_charge25` (file `StatN`, cap `10¹⁹`) and Part 177's energy event.
* **`classifier_paper_uncond_nocap25`** : the same for every `n ≥ 25 000`, with NO
  upper end; for `25 000 ≤ n < 26 000` it uses `classifier_paper_uncond_25000`, and for
  `n ≥ 26 000` the theorem `classifier_paper_uncond_nocap26` (file `EndM`).
* `uncond_nocap25_eq_172`, `uncond_nocap25_eq_178`, `uncond_nocap25_eq_30`,
  `uncond_nocap25_eq_26`: equalities proved by `rfl`; they type-check only because the
  conclusions are the same proposition.
-/

namespace BstLean.Part179

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_25000 {n : ℕ} (hn : 25000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 19) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  obtain ⟨hF0, hF1, hF2, hF⟩ := N30.N27.N26.N25.numF25 hn
  obtain ⟨hW0, hW1, hW2, hW⟩ := N30.N27.N26.N25.numW25 hn
  exact N30.N27.N26.N25.classifier_paper_gen25k hn t (Sm := SminN n) (Dm := DmN n) (Vm := VmN n)
    (Pm := 15 * PmN n) (z₁ := 211 / 100) (z₂ := 754 / 100) (by unfold SminN; positivity)
    (by norm_num) (by norm_num) z1_pow z2_pow hF0 hF1 hF2 hF
    hW0 hW1 hW2 hW (fun _ hw => N30.N27.N26.N25.stat_charge25 hn hN hw)
    (BstLean.Part160.measurableSet_agentEv (paperDesignP n) (measurableSet_SEn n))
    (SEn_ret_charge (by omega) (N40.hmomN (by omega)) passF passW measurable_passF
      measurable_passW)
    (fun c hc hτ => ⟨(N30.fb_of_SEn (by omega) hc hτ).2, (N30.fb_of_SEn (by omega) hc hτ).1⟩)

/-- **The classifier theorem with no hypothesis, for every `n ≥ 25 000` (no upper end) and every
threshold `t`**. -/
theorem classifier_paper_uncond_nocap25 {n : ℕ} (hn : 25000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  rcases lt_or_ge n 26000 with h | h
  · have hR : (n : ℝ) < 26000 := by exact_mod_cast h
    exact classifier_paper_uncond_25000 hn (by linarith) t
  · exact classifier_paper_uncond_nocap26 h t

theorem uncond_nocap25_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_nocap25 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

theorem uncond_nocap25_eq_178 {n : ℕ} (hn : 34000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_nocap25 (by omega) t =
      BstLean.Part178.classifier_paper_uncond_nocap34 hn t :=
  rfl

theorem uncond_nocap25_eq_30 {n : ℕ} (hn : 30000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_nocap25 (by omega) t = classifier_paper_uncond_nocap30 hn t :=
  rfl

theorem uncond_nocap25_eq_26 {n : ℕ} (hn : 26000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_nocap25 (by omega) t = classifier_paper_uncond_nocap26 hn t :=
  rfl

end BstLean.Part179
