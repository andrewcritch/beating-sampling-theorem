import BstLean.Part179T171
import BstLean.Part179Stat
import BstLean.Part179Num
import BstLean.Part179Q
import BstLean.Part178End34

/-!
# Part 179 (file `End`): the unconditional classifier theorem for every `n ≥ 30 000`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_30000`**: Part 172's `classifier_paper_uncond` for every `n` with
  `30 000 ≤ n ≤ 10¹⁹`: the free-threshold route `N30.classifier_paper_gen30k` (file `T171`; floor
  `sd = 0.452` and removal tolerance `η = 1/50` in the split data `N30.dP` of file `Q`; Hellinger
  split `0.00142 + 0.00503`; top `TopJ`) at the thresholds `S_m = 1/(5n)`, `D_m = 16/n³`,
  `V_m = 64/n⁴`, `P_m = 7/n⁴`, with the numerics `N30.numF30`, `N30.numW30` (file `Num`), the
  statistics charge `N30.stat_charge30` (file `Stat`, cap `10¹⁹`) and Part 177's energy event
  `agentEv (paperDesignP n) (SEn n)` (with `H_f = 1.005` on the new kept indices:
  `N30.fb_of_SEn`).
* **`classifier_paper_uncond_nocap30`** : the same for every `n ≥ 30 000`, with NO upper
  end; for `30 000 ≤ n < 34 000` it uses `classifier_paper_uncond_30000`, and for `n ≥ 34 000`
  Part 178's `classifier_paper_uncond_nocap34`.
* `uncond_nocap30_eq_172`, `uncond_nocap30_eq_178`: equalities proved by `rfl` on the common
  ranges; they type-check only because the conclusion is exactly the proposition of Part 172
  (and of Part 178).
-/

namespace BstLean.Part179

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

/-- **The classifier theorem with no hypothesis, for every `n` with `30 000 ≤ n ≤ 10¹⁹` and every
threshold `t`**: the paper's program (Lean's exact-moment form `paperDesignP`) succeeds,
`p ≤ U ≤ max(10p, 1/100)`, with probability at least `99/100` over the actual random networks
`(W, A, F)` and the program's draws. -/
theorem classifier_paper_uncond_30000 {n : ℕ} (hn : 30000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 19) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  obtain ⟨hF0, hF1, hF2, hF⟩ := N30.numF30 hn
  obtain ⟨hW0, hW1, hW2, hW⟩ := N30.numW30 hn
  exact N30.classifier_paper_gen30k hn t (Sm := SminN n) (Dm := DmN n) (Vm := VmN n)
    (Pm := 7 * PmN n) (z₁ := 211 / 100) (z₂ := 754 / 100) (by unfold SminN; positivity)
    (by norm_num) (by norm_num) z1_pow z2_pow hF0 hF1 hF2 hF
    hW0 hW1 hW2 hW (fun _ hw => N30.stat_charge30 hn hN hw)
    (BstLean.Part160.measurableSet_agentEv (paperDesignP n) (measurableSet_SEn n))
    (SEn_ret_charge (by omega) (N40.hmomN (by omega)) passF passW measurable_passF
      measurable_passW)
    (fun c hc hτ => ⟨(N30.fb_of_SEn (by omega) hc hτ).2, (N30.fb_of_SEn (by omega) hc hτ).1⟩)

/-- **The classifier theorem with no hypothesis, for every `n ≥ 30 000` (no upper end) and every
threshold `t`**. -/
theorem classifier_paper_uncond_nocap30 {n : ℕ} (hn : 30000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  rcases lt_or_ge n 34000 with h | h
  · have hR : (n : ℝ) < 34000 := by exact_mod_cast h
    exact classifier_paper_uncond_30000 hn (by linarith) t
  · exact BstLean.Part178.classifier_paper_uncond_nocap34 h t

/-- The conclusion is Part 172's (the equality type-checks only if the two propositions are the
same; it is proved by `rfl` on `80 000 ≤ n ≤ 10²⁰`). -/
theorem uncond_nocap30_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_nocap30 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

/-- The conclusion is Part 178's (proved by `rfl` on `34 000 ≤ n`). -/
theorem uncond_nocap30_eq_178 {n : ℕ} (hn : 34000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_nocap30 (by omega) t =
      BstLean.Part178.classifier_paper_uncond_nocap34 hn t :=
  rfl

/-- The conclusion of the bounded theorem is Part 178's (proved by `rfl` on
`34 000 ≤ n ≤ 10¹⁹`). -/
theorem uncond_30000_eq_178 {n : ℕ} (hn : 34000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 19) (t : ℝ) :
    classifier_paper_uncond_30000 (by omega) hN t =
      BstLean.Part178.classifier_paper_uncond_34000 hn (by linarith) t :=
  rfl

end BstLean.Part179
