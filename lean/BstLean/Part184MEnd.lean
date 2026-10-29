import BstLean.Part184MT171

/-!
# Part 184 (file `MEnd`): the end of the chain at the floor `17 500`

No proof is left open; no `native_decide` or `axiom` is used.

* `classifier_paper_uncond_17500HJ`: the chain for `n₁ ≤ n ≤ 17 750`, `n₁ ≥ 17 500`, given Lemma HQ,
  the frame junction `FREEg_stmt n₁ roomL` (`roomL = −0.0021`), `EnB_stmt` and `EnFB_stmt`.
* **`classifier_paper_uncond_17500HB`**: the same at `n₁ = 17 500`, with the room as the literal
  `-(21/10000)`. By `FREEg_mono` a frame junction at any room `ρ ≥ −0.0021` (for example `−0.0020`)
  gives this hypothesis.

A copy of the Part 184 `L` chain (floor 17 750) for every `n ≥ 17 500` (statistics cap `n ≤ 17 750`),
namespaces `….J175` / `BstLean.Part184.M`. The constants of the Lean statements are authoritative.
-/

namespace BstLean.Part184

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_17500HJ {n₁ : ℕ} (hHQ : BstLean.Part180.HQ_stmt ∧ BstLean.Part183.FREEg_stmt n₁ BstLean.Part184.M.roomL)
    (hEn : BstLean.Part184.EnB_stmt) (hFn : BstLean.Part184.EnFB_stmt) (hn₁ : 17500 ≤ n₁) {n : ℕ} (hn : n₁ ≤ n)
    (hN : (n : ℝ) ≤ 17750) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn20 : 17500 ≤ n := le_trans hn₁ hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hSm : 0 < SminN n := by unfold SminN; positivity
  obtain ⟨hF0, hF1, hF2, hF⟩ := BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J175.numF21 (n := n) hn20
  obtain ⟨hW0, hW1, hW2, hW⟩ := BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J175.numW21 (n := n) hn20
  exact BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J175.M.classifier_paper_gen22k (BstLean.Part184.M.HQG_of hHQ hEn hFn hn) (by omega) t (Sm := SminN n)
    (Dm := DmN n) (Vm := VmN n)
    (Pm := 61 * PmN n) (z₁ := 211 / 100) (z₂ := 754 / 100) hSm
    (by norm_num) (by norm_num) z1_pow z2_pow hF0 hF1 hF2 hF
    hW0 hW1 hW2 hW
    (fun _ hw => BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J175.stat_charge21 (n := n) hn20 hN hw)
    (BstLean.Part160.measurableSet_agentEv (paperDesignP n) (measurableSet_SEn n))
    (SEn_ret_charge (by omega) (N40.hmomN (by omega)) passF passW measurable_passF
      measurable_passW)
    (fun c hc hτ => ⟨(BstLean.Part179.N30.fb_of_SEn (by omega) hc hτ).2,
      (BstLean.Part179.N30.fb_of_SEn (by omega) hc hτ).1⟩)


/-- **The chain at `17 500`**: for `17 500 ≤ n ≤ 17 750`, given Lemma HQ with the frame junction
`FREEg_stmt 17500 (-(21/10000))` and the energy and location bounds `EnB_stmt`, `EnFB_stmt`. -/
theorem classifier_paper_uncond_17500HB
    (hHQ : BstLean.Part180.HQ_stmt ∧ BstLean.Part183.FREEg_stmt 17500 (-(21 / 10000)))
    (hE : BstLean.Part184.EnB_stmt) (hF : BstLean.Part184.EnFB_stmt) {n : ℕ} (hn : 17500 ≤ n)
    (hN : n ≤ 17750) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_uncond_17500HJ (n₁ := 17500) hHQ hE hF le_rfl hn (by exact_mod_cast hN) t

end BstLean.Part184

open BstLean.Part184 in
#print axioms classifier_paper_uncond_17500HJ
open BstLean.Part184 in
#print axioms classifier_paper_uncond_17500HB
