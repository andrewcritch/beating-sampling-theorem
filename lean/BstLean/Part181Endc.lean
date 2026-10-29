import BstLean.Part181T171

/-!
# Part 181 (file `Endc`): the end of the lower chain at `22 000 ≤ n ≤ 23 000`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_22000H`**: the classifier theorem for every `22 000 ≤ n ≤ 23 000`
  and every threshold `t`, with the one argument `hHQ : BstLean.Part181.HQF_stmt` (Lemma HQ and
  the frame junction at `22 000`). Statistics thresholds `S_m = 1/(5n)`, `D_m = 16/n³`,
  `V_m = 64/n⁴`, `P_m = 25/n⁴` (file `Stat`, charge `≤ 3·10⁻⁵`); bias moments `B_f = 0.01228`,
  `B_ω = 0.01273` (file `Num`); allowances `A_f = 0.0641`, `A_ω = 0.2853`, bias root `0.005154`
  (files `T169`, `T170`); ledger checked against `roomK + roomX ≥ 0.003392`.
-/

namespace BstLean.Part181

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_22000H (hHQ : HQF_stmt) {n : ℕ} (hn : 22000 ≤ n)
    (hN : (n : ℝ) ≤ 23000) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  obtain ⟨hF0, hF1, hF2, hF⟩ := BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.numF22 hn
  obtain ⟨hW0, hW1, hW2, hW⟩ := BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.numW22 hn
  exact BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.classifier_paper_gen22k hHQ hn t (Sm := SminN n)
    (Dm := DmN n) (Vm := VmN n)
    (Pm := 25 * PmN n) (z₁ := 211 / 100) (z₂ := 754 / 100) (by unfold SminN; positivity)
    (by norm_num) (by norm_num) z1_pow z2_pow hF0 hF1 hF2 hF
    hW0 hW1 hW2 hW
    (fun _ hw => BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.stat_charge22 hn hN hw)
    (BstLean.Part160.measurableSet_agentEv (paperDesignP n) (measurableSet_SEn n))
    (SEn_ret_charge (by omega) (N40.hmomN (by omega)) passF passW measurable_passF
      measurable_passW)
    (fun c hc hτ => ⟨(BstLean.Part179.N30.fb_of_SEn (by omega) hc hτ).2,
      (BstLean.Part179.N30.fb_of_SEn (by omega) hc hτ).1⟩)

end BstLean.Part181

open BstLean.Part181 in
#print axioms classifier_paper_uncond_22000H
