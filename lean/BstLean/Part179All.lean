import BstLean.Part179Q
import BstLean.Part179W20
import BstLean.Part179W128
import BstLean.Part179Top
import BstLean.Part179TopJ
import BstLean.Part179T167
import BstLean.Part179T168
import BstLean.Part179T169
import BstLean.Part179T170
import BstLean.Part179T171
import BstLean.Part179Stat
import BstLean.Part179Num
import BstLean.Part179End
import BstLean.Part179W20L
import BstLean.Part179W128L
import BstLean.Part179TopL
import BstLean.Part179TopJL
import BstLean.Part179T167L
import BstLean.Part179T168L
import BstLean.Part179T169L
import BstLean.Part179T170L
import BstLean.Part179T171L
import BstLean.Part179StatL
import BstLean.Part179NumL
import BstLean.Part179EndL
import BstLean.Part179W20M
import BstLean.Part179W128M
import BstLean.Part179TopM
import BstLean.Part179TopJM
import BstLean.Part179T167M
import BstLean.Part179T168M
import BstLean.Part179T169M
import BstLean.Part179T170M
import BstLean.Part179T171M
import BstLean.Part179StatM
import BstLean.Part179NumM
import BstLean.Part179EndM
import BstLean.Part179W20N
import BstLean.Part179W128N
import BstLean.Part179TopN
import BstLean.Part179TopJN
import BstLean.Part179T167N
import BstLean.Part179T168N
import BstLean.Part179T169N
import BstLean.Part179T170N
import BstLean.Part179T171N
import BstLean.Part179StatN
import BstLean.Part179NumN
import BstLean.Part179EndN

/-!
# Part 179: top module

No proof is left open; no `native_decide` or `axiom` is used.

Headline: `BstLean.Part179.classifier_paper_uncond_nocap25` (every `n ≥ 25 000`, every `t`, no
hypothesis). It is assembled from four chains: `N30` (files without suffix, `30 000 ≤ n`),
`N30.N27` (suffix `L`, `27 000 ≤ n`), `N30.N27.N26` (suffix `M`, `26 000 ≤ n`) and
`N30.N27.N26.N25` (suffix `N`, `25 000 ≤ n`), with Part 178's theorem for `n ≥ 34 000`.
-/

#print axioms BstLean.Part179.classifier_paper_uncond_nocap25
#print axioms BstLean.Part179.classifier_paper_uncond_25000
#print axioms BstLean.Part179.uncond_nocap25_eq_172
#print axioms BstLean.Part179.uncond_nocap25_eq_178
#print axioms BstLean.Part179.uncond_nocap25_eq_30
#print axioms BstLean.Part179.uncond_nocap25_eq_26
#print axioms BstLean.Part179.N30.N27.N26.N25.root_core25
#print axioms BstLean.Part179.N30.N27.N26.N25.roomK_ge
#print axioms BstLean.Part179.N30.N27.N26.N25.classifier_paper_JM49n
#print axioms BstLean.Part179.N30.N27.N26.N25.LJ_proved
#print axioms BstLean.Part179.N30.N27.N26.N25.PB_leE
#print axioms BstLean.Part179.N30.N27.N26.N25.classifier_paper_gen25k
#print axioms BstLean.Part179.N30.N27.N26.N25.stat_charge25
#print axioms BstLean.Part179.N30.N27.N26.N25.numF25
#print axioms BstLean.Part179.N30.N27.N26.N25.numW25
#print axioms BstLean.Part179.W20_le_25
#print axioms BstLean.Part179.W128_le_25
#print axioms BstLean.Part179.classifier_paper_uncond_nocap26
#print axioms BstLean.Part179.classifier_paper_uncond_26000
#print axioms BstLean.Part179.uncond_nocap26_eq_172
#print axioms BstLean.Part179.uncond_nocap26_eq_178
#print axioms BstLean.Part179.uncond_nocap26_eq_30
#print axioms BstLean.Part179.uncond_nocap26_eq_27
#print axioms BstLean.Part179.classifier_paper_uncond_nocap27
#print axioms BstLean.Part179.classifier_paper_uncond_27000
#print axioms BstLean.Part179.classifier_paper_uncond_nocap30
#print axioms BstLean.Part179.classifier_paper_uncond_30000
#print axioms BstLean.Part179.uncond_nocap30_eq_172
#print axioms BstLean.Part179.uncond_nocap30_eq_178
#print axioms BstLean.Part179.N30.dStar_ge
#print axioms BstLean.Part179.N30.Sb_lower
#print axioms BstLean.Part179.W20_le_30
#print axioms BstLean.Part179.W128_le_30
#print axioms BstLean.Part179.N30.betaMP_452_30
#print axioms BstLean.Part179.N30.root_core30
#print axioms BstLean.Part179.N30.cert_charge528
#print axioms BstLean.Part179.N30.classifier_paper_JM48
#print axioms BstLean.Part179.N30.LJ_proved
#print axioms BstLean.Part179.N30.PB_leE
#print axioms BstLean.Part179.N30.classifier_paper_gen30k
#print axioms BstLean.Part179.N30.stat_charge30
#print axioms BstLean.Part179.N30.numF30
#print axioms BstLean.Part179.N30.numW30
#print axioms BstLean.Part179.N30.N27.betaMP_452_27
#print axioms BstLean.Part179.N30.N27.root_core27
#print axioms BstLean.Part179.N30.N27.classifier_paper_JM49
#print axioms BstLean.Part179.N30.N27.classifier_paper_gen27k
#print axioms BstLean.Part179.N30.N27.stat_charge27
#print axioms BstLean.Part179.N30.N27.N26.root_core26
#print axioms BstLean.Part179.N30.N27.N26.classifier_paper_JM49m
#print axioms BstLean.Part179.N30.N27.N26.classifier_paper_gen26k
#print axioms BstLean.Part179.N30.N27.N26.stat_charge26
