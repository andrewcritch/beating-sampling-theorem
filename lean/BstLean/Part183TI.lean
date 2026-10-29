import BstLean.Part183TSNum
import BstLean.Part182TImono

/-!
# Part 183 (file `TI`): Lemma TI ("TI-lite") for every `n ≥ 20 000` on `0.378 ≤ x·x' ≤ 0.646`

No proof is left open; no `native_decide` or `axiom` is used.

**`TI_lite_20000`**: `TI_hyp n 0.378 0.646 0.73 10⁻¹⁸` for every `n ≥ 20 000`, from Part 182's
assembly `ta_TI46` with the numerics of files `TENum`, `TSNum` (`k_E = 0.72`, `k_o = 0.026`,
`k_s = 0.18`, `η = 24/100000`): `λ = ta_lam(0.72, 0.026, 0.18) ≈ 0.7213 ≤ 0.73`.
-/

namespace BstLean.Part183

theorem TI_lite_20000 {n : ℕ} (hn : 20000 ≤ n) :
    BstLean.Part182.TI_hyp n (378 / 1000) (646 / 1000) (73 / 100) (1 / 10 ^ 18) :=
  BstLean.Part182.TI_hyp_mono BstLean.Part183.T.tsn_lam le_rfl (BstLean.Part183.T.tsn_TI hn)

end BstLean.Part183

open BstLean.Part183 in
#print axioms TI_lite_20000
