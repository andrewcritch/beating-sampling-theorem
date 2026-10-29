import BstLean.Part180Split
import BstLean.Part180HQFl

/-!
# Part 180 (file `HQS`): `HQ_stmt` is proved

No proof is left open; no `native_decide` or `axiom` is used.

* **`hq_proved : HQ_stmt`**: the statement of Lemma HQ in the latitude-moment interface (file
  `Split`), from `fluct_of_latMom_hq` (file `HQFl`).
-/

namespace BstLean.Part180

/-- **Lemma HQ in the latitude-moment interface is proved.** -/
theorem hq_proved : HQ_stmt := by
  intro n hn D c t wl ws σl η hwl hws hσl h0 h1 hcA CA hCA hε q P lam lam' hl0 hl1 hl0' hl1' hfl hsum
  exact fluct_of_latMom_hq hn D c t hwl hws hσl h0 h1 hcA hCA hε P hl0 hl1 hl0' hl1' hsum

end BstLean.Part180
