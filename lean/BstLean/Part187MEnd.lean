import BstLean.Part187MT171

/-!
# Part 187 (file `MEnd`): the end of the chain at the floor `16 250`

No proof is left open; no `native_decide` or `axiom` is used.

* `classifier_paper_uncond_16250HJ`: the chain for `n₁ ≤ n ≤ 16 384`, `n₁ ≥ 16 250`, given Lemma HQ,
  the frame junction `FREEg_stmt n₁ roomL` (`roomL = −0.002212`), `EnB_stmt`, `EnFB_stmt` and the
  row-averaged bias moments `BiasRA81_stmt` (`P_m = 81/n⁴`).
* **`classifier_paper_uncond_16250HB`**: the same at `n₁ = 16 250`, with the room as the literal
  `-(2212/1000000)`, which `BstLean.Part187.FREE16250K_proved` provides.

A copy of the Part 186 `L` chain re-tuned for `16 250 ≤ n ≤ 16 384` (statistics cap `16 384`), with
the bias moments `194/n`, `148/n` (row averaging) and the piN threshold `P_m = 81/n⁴`; namespace
`….J1725.J17.J1625`. The constants of the Lean statements are authoritative.
-/

namespace BstLean.Part187

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_16250HJ {n₁ : ℕ}
    (hHQ : BstLean.Part180.HQ_stmt ∧ BstLean.Part183.FREEg_stmt n₁ BstLean.Part187.M.roomL)
    (hEn : BstLean.Part184.EnB_stmt) (hFn : BstLean.Part184.EnFB_stmt)
    (hRA : BstLean.Part187.M.BiasRA81_stmt) (hn₁ : 16250 ≤ n₁) {n : ℕ} (hn : n₁ ≤ n)
    (hN : (n : ℝ) ≤ 16384) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn20 : 16250 ≤ n := le_trans hn₁ hn
  exact BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J1725.J17.J1625.M.classifier_paper_RA
    (BstLean.Part187.M.HQG_of hHQ hEn hFn hn) hn20 t hRA
    (fun _ hw => BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J1725.J17.J1625.stat_charge21 (n := n) hn20 hN hw)
    (BstLean.Part160.measurableSet_agentEv (paperDesignP n) (measurableSet_SEn n))
    (BstLean.Part177.R.SEn_ret_charge (by omega) (BstLean.Part177.N40.R.hmomN (by omega)) passF passW measurable_passF
      measurable_passW)
    (fun c hc hτ => ⟨(BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J1725.fb_of_SEn (by omega) hc hτ).2,
      (BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J1725.fb_of_SEn (by omega) hc hτ).1⟩)

/-- **The chain at `16 250`**: for `16 250 ≤ n ≤ 16 384`, given Lemma HQ with the frame junction
`FREEg_stmt 16250 (-(2212/1000000))`, `EnB_stmt`, `EnFB_stmt` and `BiasRA81_stmt` (`P_m = 81/n⁴`). -/
theorem classifier_paper_uncond_16250HB
    (hHQ : BstLean.Part180.HQ_stmt ∧ BstLean.Part183.FREEg_stmt 16250 (-(2212 / 1000000)))
    (hE : BstLean.Part184.EnB_stmt) (hF : BstLean.Part184.EnFB_stmt)
    (hRA : BstLean.Part187.M.BiasRA81_stmt) {n : ℕ} (hn : 16250 ≤ n)
    (hN : n ≤ 16384) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_uncond_16250HJ (n₁ := 16250) hHQ hE hF hRA le_rfl hn (by exact_mod_cast hN) t

end BstLean.Part187

open BstLean.Part187 in
#print axioms classifier_paper_uncond_16250HJ
open BstLean.Part187 in
#print axioms classifier_paper_uncond_16250HB
