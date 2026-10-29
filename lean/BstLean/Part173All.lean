import BstLean.Part173P172
import BstLean.Part173T172

/-!
# Part 173: the unconditional Lean classifier theorem for every `59 000 ≤ n ≤ 10²⁰`

No proof is left open; no `native_decide` or `axiom` is used.

Two copies of the Part 165–172 chain, with the numeric side conditions repaired:

* `Part173Root`, `Part173P166` … `Part173P172` (namespace `BstLean.Part173`): every `n ≥ 70 000`,
  with retuned constants only; end theorem `classifier_paper_uncond70k`.
* `Part173Root59`, `Part173T166` … `Part173T172` (namespace `BstLean.Part173.N59`): every
  `n ≥ 59 000`. Beyond retuned constants it uses (1) the NEW latitude factor `1 − s² ≤ 0.5743` in
  both fluctuation allowances (`Part173Def`: `FflQ`, `WflQ`; `Part173Cov`: `tanSq_le_lat`,
  `cov_bound_lat`, `exFn_mom_q`, `exWn_mom_q`), (2) `q = ⌊log₂ n⌋ = 15` with `128q ≤ 0.034n`
  (`q_lin59`), (3) the latitude moment `Θ = 0.6222` with the certificate charge `17·10⁻⁴` and the
  room `roomE59 = roomC − 17·10⁻⁴`; end theorem `N59.classifier_paper_uncond59k`.

Headline: **`BstLean.Part173.classifier_paper_uncond_59000`** (below).
-/

namespace BstLean.Part173

open BstLean.Part130 BstLean.Part157 BstLean.Part169

/-- **The classifier theorem with no remaining hypothesis, for every `n` with
`59 000 ≤ n ≤ 10²⁰` and every threshold `t`**: the paper's program (Lean's exact-moment form
`paperDesignP`) succeeds, `p ≤ U ≤ max(10p, 1/100)`, with probability at least `99/100` over the
actual random networks `(W, A, F)` and the program's draws. Part 172 had `80 000 ≤ n`. -/
theorem classifier_paper_uncond_59000 {n : ℕ} (hn : 59000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  N59.classifier_paper_uncond59k hn hN t

end BstLean.Part173

#print axioms BstLean.Part173.classifier_paper_uncond_59000
#print axioms BstLean.Part173.N59.classifier_paper_uncond59k
#print axioms BstLean.Part173.N59.stat_charge
#print axioms BstLean.Part173.N59.classifier_paper_final59k
#print axioms BstLean.Part173.N59.classifier_paper_bias_num59k
#print axioms BstLean.Part173.N59.classifier_paper_A59k
#print axioms BstLean.Part173.N59.classifier_paper_LG59k
#print axioms BstLean.Part173.N59.classifier_paper_JM47
#print axioms BstLean.Part173.N59.classifier_paper_root59k
#print axioms BstLean.Part173.N59.root_core59
#print axioms BstLean.Part173.N59.betaM_4691_59
#print axioms BstLean.Part173.N59.W128_le
#print axioms BstLean.Part173.N59.theta_mom
#print axioms BstLean.Part173.N59.cert_charge_47
#print axioms BstLean.Part173.N59.roomE59_ge
#print axioms BstLean.Part173.N59.q_lin59
#print axioms BstLean.Part173.N59.K2_num
#print axioms BstLean.Part173.N59.PB_le
#print axioms BstLean.Part173.N59.qB_pos
#print axioms BstLean.Part173.N59.node_lat_q
#print axioms BstLean.Part173.N59.FflQ_le
#print axioms BstLean.Part173.N59.WflQ_le
#print axioms BstLean.Part173.N59.numF
#print axioms BstLean.Part173.N59.numW
#print axioms BstLean.Part173.N59.sg_node_lat
#print axioms BstLean.Part173.N59.sig_charge
#print axioms BstLean.Part173.N59.fr_X_num
#print axioms BstLean.Part173.N59.en_num59
#print axioms BstLean.Part173.tanSq_le_lat
#print axioms BstLean.Part173.cov_bound_lat
#print axioms BstLean.Part173.exFn_mom_q
#print axioms BstLean.Part173.exWn_mom_q
#print axioms BstLean.Part173.classifier_paper_uncond70k
#print axioms BstLean.Part173.classifier_paper_root70k
#print axioms BstLean.Part173.PB_le
#print axioms BstLean.Part173.Wfl_le
#print axioms BstLean.Part173.stat_charge
