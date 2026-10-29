import BstLean.Part182T171x21M

/-!
# Part 182 (file `Endc21M`) [TI-lite (λ = 0.72) copy: `roomT21M = 0.0018`, `HQF21M_stmt`, namespace `….N21.M`]: the end of the lower chain at `21 500 ≤ n ≤ 22 000`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_21500HM`**: the classifier theorem for every `21 500 ≤ n ≤ 22 000`
  and every threshold `t`, with the one argument `hHQ : BstLean.Part182.HQF21M_stmt` (Lemma HQ and
  the frame junction at `21 000`; the top needs `n ≥ 21 500`). Statistics thresholds `S_m = 1/(5n)`, `D_m = 16/n³`,
  `V_m = 64/n⁴`, `P_m = 30/n⁴` (file `Stat21`, charge `≤ 3.6·10⁻⁵`); bias moments `B_f = 0.01286`,
  `B_ω = 0.01334` (file `Num21`); allowances `A_f = 0.0628`, `A_ω = 0.2778`, bias root `0.005154`
  (files `T169x21`, `T170x21`); ledger `≈ 5.153·10⁻³ ≤ 0.00516`.
-/

namespace BstLean.Part182

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_21500HM (hHQ : HQF21M_stmt) {n : ℕ} (hn : 21500 ≤ n)
    (hN : (n : ℝ) ≤ 22000) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  obtain ⟨hF0, hF1, hF2, hF⟩ := BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.N21.numF21 (n := n) (by omega)
  obtain ⟨hW0, hW1, hW2, hW⟩ := BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.N21.numW21 (n := n) (by omega)
  exact BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.N21.M.classifier_paper_gen22k hHQ hn t (Sm := SminN n)
    (Dm := DmN n) (Vm := VmN n)
    (Pm := 30 * PmN n) (z₁ := 211 / 100) (z₂ := 754 / 100) (by unfold SminN; positivity)
    (by norm_num) (by norm_num) z1_pow z2_pow hF0 hF1 hF2 hF
    hW0 hW1 hW2 hW
    (fun _ hw => BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.N21.stat_charge21 (n := n) (by omega) hN hw)
    (BstLean.Part160.measurableSet_agentEv (paperDesignP n) (measurableSet_SEn n))
    (SEn_ret_charge (by omega) (N40.hmomN (by omega)) passF passW measurable_passF
      measurable_passW)
    (fun c hc hτ => ⟨(BstLean.Part179.N30.fb_of_SEn (by omega) hc hτ).2,
      (BstLean.Part179.N30.fb_of_SEn (by omega) hc hτ).1⟩)

end BstLean.Part182

open BstLean.Part182 in
#print axioms classifier_paper_uncond_21500HM
