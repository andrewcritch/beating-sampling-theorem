import BstLean.Part178T171
import BstLean.Part178Stat
import BstLean.Part178Num
import BstLean.Part178Q
import BstLean.Part177End40

/-!
# Part 178 (file `End`): the unconditional classifier theorem for every `n ≥ 36 000`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_36000`**: Part 172's `classifier_paper_uncond` for every `n` with
  `36 000 ≤ n ≤ 10²⁰`: the free-threshold route `N36.classifier_paper_gen36k` (file `T171`; removal
  tolerance `η = 1/50` in the split data `N36.dP` of file `Q`; Hellinger split `0.00235 + 0.0041`;
  top `TopJ`) at the thresholds `S_m = 1/(5n)`, `D_m = 16/n³`, `V_m = 64/n⁴`, `P_m = 4/n⁴`, with
  the numerics `N36.numF36`, `N36.numW36` (file `Num`), the statistics charge `N36.stat_charge36`
  (file `Stat`) and Part 177's energy event `agentEv (paperDesignP n) (SEn n)` (with `H_f = 1.005`
  on the new kept indices: `N36.fb_of_SEn`).
* **`classifier_paper_uncond_nocap36`** (headline): the same for every `n ≥ 36 000`, with NO upper
  end; for `n ≥ 10²⁰` it uses Part 174's `Cap.classifier_paper_uncond_large`.
* `uncond_nocap36_eq_172`, `uncond_nocap36_eq_177`: the proof terms are equal by `rfl` on the
  common ranges; so the conclusion is exactly the proposition of Part 172 (and of Part 177).
-/

namespace BstLean.Part178

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

/-- **The classifier theorem with no hypothesis, for every `n` with `36 000 ≤ n ≤ 10²⁰` and every
threshold `t`**: the paper's program (Lean's exact-moment form `paperDesignP`) succeeds,
`p ≤ U ≤ max(10p, 1/100)`, with probability at least `99/100` over the actual random networks
`(W, A, F)` and the program's draws. -/
theorem classifier_paper_uncond_36000 {n : ℕ} (hn : 36000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  obtain ⟨hF0, hF1, hF2, hF⟩ := N36.numF36 hn
  obtain ⟨hW0, hW1, hW2, hW⟩ := N36.numW36 hn
  exact N36.classifier_paper_gen36k hn t (Sm := SminN n) (Dm := DmN n) (Vm := VmN n)
    (Pm := 4 * PmN n) (z₁ := 211 / 100) (z₂ := 754 / 100) (by unfold SminN; positivity)
    (by norm_num) (by norm_num) z1_pow z2_pow hF0 hF1 hF2 hF
    hW0 hW1 hW2 hW (fun _ hw => N36.stat_charge36 hn hN hw)
    (BstLean.Part160.measurableSet_agentEv (paperDesignP n) (measurableSet_SEn n))
    (SEn_ret_charge (by omega) (N40.hmomN (by omega)) passF passW measurable_passF
      measurable_passW)
    (fun c hc hτ => ⟨(N36.fb_of_SEn (by omega) hc hτ).2, (N36.fb_of_SEn (by omega) hc hτ).1⟩)

/-- **The classifier theorem with no hypothesis, for every `n ≥ 36 000` (no upper end) and every
threshold `t`** (Part 178's headline). -/
theorem classifier_paper_uncond_nocap36 {n : ℕ} (hn : 36000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  rcases le_total (n : ℝ) (10 ^ 20) with h | h
  · exact classifier_paper_uncond_36000 hn h t
  · exact BstLean.Part174.Cap.classifier_paper_uncond_large (le_trans (by norm_num) h) t

/-- The conclusion is Part 172's (proofs equal by `rfl` on `80 000 ≤ n ≤ 10²⁰`). -/
theorem uncond_nocap36_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_nocap36 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

/-- The conclusion is Part 177's (proofs equal by `rfl` on `40 000 ≤ n`). -/
theorem uncond_nocap36_eq_177 {n : ℕ} (hn : 40000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_nocap36 (by omega) t =
      BstLean.Part177.classifier_paper_uncond_nocap40 hn t :=
  rfl

end BstLean.Part178
