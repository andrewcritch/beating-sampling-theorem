import BstLean.Part188All
import BstLean.Part190MT171



namespace BstLean.Part190
open BstLean.Part188
open BstLean.Part187

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_16200HJ {n₁ : ℕ}
    (hHQ : BstLean.Part180.HQ_stmt ∧ BstLean.Part183.FREEg_stmt n₁ BstLean.Part188.M.roomL)
    (hEn : BstLean.Part184.EnB_stmt) (hFn : BstLean.Part184.EnFB_stmt)
    (hRA : BstLean.Part190.M.BiasRA82_stmt) (hn₁ : 16200 ≤ n₁) {n : ℕ} (hn : n₁ ≤ n)
    (hN : (n : ℝ) ≤ 16384) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn20 : 16200 ≤ n := le_trans hn₁ hn
  exact BstLean.Part190.Chain.M.classifier_paper_RA
    (BstLean.Part188.M.HQG_of hHQ hEn hFn hn) hn20 t hRA
    (fun _ hw => BstLean.Part188.Chain.stat_charge21 (n := n) hn20 hN hw)
    (BstLean.Part160.measurableSet_agentEv (paperDesignP n) (measurableSet_SEn n))
    (BstLean.Part188.Base177_R.SEn_ret_charge (by omega) (BstLean.Part188.Base177_N40_R.hmomN (by omega)) passF passW measurable_passF
      measurable_passW)
    (fun c hc hτ => ⟨(BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J1725.fb_of_SEn (by omega) hc hτ).2,
      (BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J1725.fb_of_SEn (by omega) hc hτ).1⟩)


theorem classifier_paper_uncond_16200HB
    (hHQ : BstLean.Part180.HQ_stmt ∧ BstLean.Part183.FREEg_stmt 16200 (-(2212 / 1000000)))
    (hE : BstLean.Part184.EnB_stmt) (hF : BstLean.Part184.EnFB_stmt)
    (hRA : BstLean.Part190.M.BiasRA82_stmt) {n : ℕ} (hn : 16200 ≤ n)
    (hN : n ≤ 16384) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_uncond_16200HJ (n₁ := 16200) hHQ hE hF hRA le_rfl hn (by exact_mod_cast hN) t

end BstLean.Part190

open BstLean.Part190 in
#print axioms classifier_paper_uncond_16200HJ
open BstLean.Part190 in
#print axioms classifier_paper_uncond_16200HB
