import BstLean.Part184CT171

/-!
# Part 184 (file `CEnd`): the end of the chain at the floor `18 500`

No proof is left open; no `native_decide` or `axiom` is used.

* `classifier_paper_uncond_18500HJ`: the chain for `n₁ ≤ n ≤ 19 000`, `n₁ ≥ 18 500`, given Lemma HQ,
  the frame junction `FREEg_stmt n₁ roomT185` and `EnB_stmt`.
* **`classifier_paper_uncond_18500HB`**: the same at `n₁ = 18 500` with `HQF185_stmt`.

A copy of the Part 183 `K` chain (floor 19 000) for every `n ≥ 18 500` (statistics cap `n ≤ 19 000`),
namespaces `….J185` / `BstLean.Part184.C`, with `EnB_stmt`/`WflB` in place of `EnJ_stmt`/`WflJ`.
The constants of the Lean statements are authoritative; docstrings of copied lemmas can carry older
numbers.
-/

namespace BstLean.Part184

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_18500HJ {n₁ : ℕ} (hHQ : BstLean.Part180.HQ_stmt ∧ BstLean.Part183.FREEg_stmt n₁ BstLean.Part184.roomT185)
    (hEn : BstLean.Part184.EnB_stmt) (hn₁ : 18500 ≤ n₁) {n : ℕ} (hn : n₁ ≤ n)
    (hN : (n : ℝ) ≤ 19000) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn20 : 18500 ≤ n := le_trans hn₁ hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hSm : 0 < SminN n := by unfold SminN; positivity
  obtain ⟨hF0, hF1, hF2, hF⟩ := BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J185.numF21 (n := n) hn20
  obtain ⟨hW0, hW1, hW2, hW⟩ := BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J185.numW21 (n := n) hn20
  exact BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J185.M.classifier_paper_gen22k (BstLean.Part184.C.HQG_of hHQ hEn hn) (by omega) t (Sm := SminN n)
    (Dm := DmN n) (Vm := VmN n)
    (Pm := 49 * PmN n) (z₁ := 211 / 100) (z₂ := 754 / 100) hSm
    (by norm_num) (by norm_num) z1_pow z2_pow hF0 hF1 hF2 hF
    hW0 hW1 hW2 hW
    (fun _ hw => BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J185.stat_charge21 (n := n) hn20 hN hw)
    (BstLean.Part160.measurableSet_agentEv (paperDesignP n) (measurableSet_SEn n))
    (SEn_ret_charge (by omega) (N40.hmomN (by omega)) passF passW measurable_passF
      measurable_passW)
    (fun c hc hτ => ⟨(BstLean.Part179.N30.fb_of_SEn (by omega) hc hτ).2,
      (BstLean.Part179.N30.fb_of_SEn (by omega) hc hτ).1⟩)


/-- **The chain at `18 500`**: for `18 500 ≤ n ≤ 19 000`, given Lemma HQ with the frame junction
`FREE185_stmt` (`HQF185_stmt`) and the energy bound `EnB_stmt`, the classifier theorem holds. -/
theorem classifier_paper_uncond_18500HB (hHQ : BstLean.Part184.HQF185_stmt)
    (hE : BstLean.Part184.EnB_stmt) {n : ℕ} (hn : 18500 ≤ n) (hN : n ≤ 19000) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_uncond_18500HJ (n₁ := 18500) hHQ hE le_rfl hn (by exact_mod_cast hN) t

end BstLean.Part184

open BstLean.Part184 in
#print axioms classifier_paper_uncond_18500HJ
open BstLean.Part184 in
#print axioms classifier_paper_uncond_18500HB
