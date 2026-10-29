import BstLean.Part186KT171

/-!
# Part 186 (file `KEnd`): the end of the chain at the floor `16 500`

No proof is left open; no `native_decide` or `axiom` is used.

* `classifier_paper_uncond_16500HJ`: the chain for `n₁ ≤ n ≤ 17 000`, `n₁ ≥ 16 500`, given Lemma HQ,
  the frame junction `FREEg_stmt n₁ roomL` (`roomL = −0.002691`), `EnB_stmt`, `EnFB_stmt` and the
  row-averaged bias moments `BiasRA80_stmt`.
* **`classifier_paper_uncond_16500HB`**: the same at `n₁ = 16 500`, with the room as the literal
  `-(2691/1000000)`. By `FREEg_mono` a frame junction at any room `ρ ≥ −0.002691` gives this
  hypothesis.

A copy of the Part 185 `K` chain re-tuned for `16 500 ≤ n ≤ 17 000` (statistics cap `17 000`), with
the bias moments `194/n`, `148/n` (row averaging) and the piN threshold `P_m = 80/n⁴`; namespaces
`….J1725.J17.J165` / `BstLean.Part186.K`. The constants of the Lean statements are authoritative.
-/

namespace BstLean.Part186

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_16500HJ {n₁ : ℕ}
    (hHQ : BstLean.Part180.HQ_stmt ∧ BstLean.Part183.FREEg_stmt n₁ BstLean.Part186.K.roomL)
    (hEn : BstLean.Part184.EnB_stmt) (hFn : BstLean.Part184.EnFB_stmt)
    (hRA : BstLean.Part186.K.BiasRA80_stmt) (hn₁ : 16500 ≤ n₁) {n : ℕ} (hn : n₁ ≤ n)
    (hN : (n : ℝ) ≤ 17000) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn20 : 16500 ≤ n := le_trans hn₁ hn
  exact BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J1725.J17.J165.M.classifier_paper_RA
    (BstLean.Part186.K.HQG_of hHQ hEn hFn hn) hn20 t hRA
    (fun _ hw => BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J1725.J17.J165.stat_charge21 (n := n) hn20 hN hw)
    (BstLean.Part160.measurableSet_agentEv (paperDesignP n) (measurableSet_SEn n))
    (SEn_ret_charge (by omega) (N40.hmomN (by omega)) passF passW measurable_passF
      measurable_passW)
    (fun c hc hτ => ⟨(BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J1725.fb_of_SEn (by omega) hc hτ).2,
      (BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J1725.fb_of_SEn (by omega) hc hτ).1⟩)

/-- **The chain at `16 500`**: for `16 500 ≤ n ≤ 17 000`, given Lemma HQ with the frame junction
`FREEg_stmt 16500 (-(2691/1000000))`, `EnB_stmt`, `EnFB_stmt` and `BiasRA80_stmt`. -/
theorem classifier_paper_uncond_16500HB
    (hHQ : BstLean.Part180.HQ_stmt ∧ BstLean.Part183.FREEg_stmt 16500 (-(2691 / 1000000)))
    (hE : BstLean.Part184.EnB_stmt) (hF : BstLean.Part184.EnFB_stmt)
    (hRA : BstLean.Part186.K.BiasRA80_stmt) {n : ℕ} (hn : 16500 ≤ n)
    (hN : n ≤ 17000) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_uncond_16500HJ (n₁ := 16500) hHQ hE hF hRA le_rfl hn (by exact_mod_cast hN) t

end BstLean.Part186

open BstLean.Part186 in
#print axioms classifier_paper_uncond_16500HJ
open BstLean.Part186 in
#print axioms classifier_paper_uncond_16500HB
