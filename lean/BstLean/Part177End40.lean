import BstLean.Part177T171b
import BstLean.Part177Stat40
import BstLean.Part177Num40
import BstLean.Part177En
import BstLean.Part177TopJ40
import BstLean.Part177End

/-!
# Part 177 (file `End40`): the unconditional classifier theorem for every `n ≥ 40 000`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_40000`**: Part 172's `classifier_paper_uncond` for every `n` with
  `40 000 ≤ n ≤ 10²⁰`: the free-threshold route `N40.classifier_paper_gen40k` (file `T171b`; Hellinger split `0.003554 + 0.0029` through file `Split`, top `TopJ40`) at the
  thresholds `S_m = 1/(5n)`, `D_m = 16/n³`, `V_m = 64/n⁴`, `P_m = 3/n⁴`, with the numerics
  `N40.numF40`, `N40.numW40` (file `Num40`), the statistics charge `N40.stat_charge40` (file `Stat40`)
  and the energy event `agentEv (paperDesignP n) (SEn n)` (file `En`; charge `10⁻⁶` from the
  moment bound of file `EnMom`; `H_f = 1.005`).
* **`classifier_paper_uncond_nocap40`** (headline): the same for every `n ≥ 40 000`, with NO upper
  end; for `n ≥ 10²⁰` it uses Part 174's `Cap.classifier_paper_uncond_large` (`n ≥ 10¹⁹`).
* `uncond_nocap40_eq_172`, `uncond_nocap40_eq_176`: the proof terms are equal by `rfl` on the
  common ranges; so the conclusion is exactly the proposition of Part 172 (and of Part 176); `uncond_nocap40_eq_43` relates it to the 43 000 theorem of file `End`.
-/

namespace BstLean.Part177

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171

/-- **The classifier theorem with no hypothesis, for every `n` with `40 000 ≤ n ≤ 10²⁰` and every
threshold `t`**: the paper's program (Lean's exact-moment form `paperDesignP`) succeeds,
`p ≤ U ≤ max(10p, 1/100)`, with probability at least `99/100` over the actual random networks
`(W, A, F)` and the program's draws. -/
theorem classifier_paper_uncond_40000 {n : ℕ} (hn : 40000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  obtain ⟨hF0, hF1, hF2, hF⟩ := N40.numF40 hn
  obtain ⟨hW0, hW1, hW2, hW⟩ := N40.numW40 hn
  exact N40.classifier_paper_gen40k hn t (Sm := SminN n) (Dm := DmN n) (Vm := VmN n)
    (Pm := 3 * PmN n) (z₁ := 211 / 100) (z₂ := 754 / 100) (by unfold SminN; positivity)
    (by norm_num) (by norm_num) z1_pow z2_pow hF0 hF1 hF2 hF
    hW0 hW1 hW2 hW (fun _ hw => N40.stat_charge40 hn hN hw)
    (BstLean.Part160.measurableSet_agentEv (paperDesignP n) (measurableSet_SEn n))
    (SEn_ret_charge (by omega) (N40.hmomN (by omega)) passF passW measurable_passF
      measurable_passW)
    (fun c hc hτ => ⟨(fb_of_SEn (by omega) hc hτ).2, (fb_of_SEn (by omega) hc hτ).1⟩)

/-- **The classifier theorem with no hypothesis, for every `n ≥ 40 000` (no upper end) and every
threshold `t`** (Part 177's headline). -/
theorem classifier_paper_uncond_nocap40 {n : ℕ} (hn : 40000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  rcases le_total (n : ℝ) (10 ^ 20) with h | h
  · exact classifier_paper_uncond_40000 hn h t
  · exact BstLean.Part174.Cap.classifier_paper_uncond_large (le_trans (by norm_num) h) t

/-- The conclusion is Part 172's (proofs equal by `rfl` on `80 000 ≤ n ≤ 10²⁰`). -/
theorem uncond_nocap40_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_nocap40 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

/-- The conclusion is Part 176's (proofs equal by `rfl` on `45 000 ≤ n`). -/
theorem uncond_nocap40_eq_176 {n : ℕ} (hn : 45000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_nocap40 (by omega) t =
      BstLean.Part176.classifier_paper_uncond_nocap45 hn t :=
  rfl

end BstLean.Part177

namespace BstLean.Part177

/-- The conclusion is Part 177's 43 000 theorem (proofs equal by `rfl` on `43 000 ≤ n`). -/
theorem uncond_nocap40_eq_43 {n : ℕ} (hn : 43000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_nocap40 (by omega) t = classifier_paper_uncond_nocap43 hn t :=
  rfl

end BstLean.Part177
