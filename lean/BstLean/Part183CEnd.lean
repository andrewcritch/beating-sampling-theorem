import BstLean.Part183CT171

/-!
# Part 183 (file `CEnd`): the end of the chain: `classifier_paper_uncond_20000HJ`.

No proof is left open; no `native_decide` or `axiom` is used.

A copy of the Part 182 `*21M` series for every `n ≥ 20 000` (statistics cap `n ≤ 21 500`), namespace
`….J20` / `BstLean.Part183.C`. The constants above are those of the Lean statements; the
docstrings of copied lemmas can carry older numbers, and the Lean statements are authoritative.
-/

namespace BstLean.Part183

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_20000HJ {n₁ : ℕ} (hHQ : BstLean.Part183.HQFn_stmt n₁)
    (hEn : BstLean.Part183.EnJ_stmt) (hn₁ : 20000 ≤ n₁) {n : ℕ} (hn : n₁ ≤ n)
    (hN : (n : ℝ) ≤ 21500) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn20 : 20000 ≤ n := le_trans hn₁ hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hSm : 0 < SminN n := by unfold SminN; positivity
  obtain ⟨hF0, hF1, hF2, hF⟩ := BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J20.numF21 (n := n) hn20
  obtain ⟨hW0, hW1, hW2, hW⟩ := BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J20.numW21 (n := n) hn20
  exact BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J20.M.classifier_paper_gen22k (BstLean.Part183.C.HQG_of hHQ hEn hn) (by omega) t (Sm := SminN n)
    (Dm := DmN n) (Vm := VmN n)
    (Pm := 36 * PmN n) (z₁ := 211 / 100) (z₂ := 754 / 100) hSm
    (by norm_num) (by norm_num) z1_pow z2_pow hF0 hF1 hF2 hF
    hW0 hW1 hW2 hW
    (fun _ hw => BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J20.stat_charge21 (n := n) hn20 hN hw)
    (BstLean.Part160.measurableSet_agentEv (paperDesignP n) (measurableSet_SEn n))
    (SEn_ret_charge (by omega) (N40.hmomN (by omega)) passF passW measurable_passF
      measurable_passW)
    (fun c hc hτ => ⟨(BstLean.Part179.N30.fb_of_SEn (by omega) hc hτ).2,
      (BstLean.Part179.N30.fb_of_SEn (by omega) hc hτ).1⟩)

end BstLean.Part183

open BstLean.Part183 in
#print axioms classifier_paper_uncond_20000HJ
