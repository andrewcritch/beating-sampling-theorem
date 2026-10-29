import BstLean.Part183USNum
import BstLean.Part182TImono

/-!
# Part 183 (file `UI`): Lemma TI ("TI-lite") for every `n ≥ 19 000` on `0.374 ≤ x·x' ≤ 0.65`

No proof is left open; no `native_decide` or `axiom` is used.

**`TI_lite_19000`**: `TI_hyp n 0.374 0.65 0.73 10⁻¹⁸` for every `n ≥ 19 000`, from Part 182's
assembly `ta_TI46` with the numerics of files `UENum`, `USNum` (`k_E = 0.725`, `k_o = 0.027`,
`k_s = 0.182`, `η = 253/10⁶`): `λ = ta_lam(0.725, 0.027, 0.182) ≈ 0.7264 ≤ 0.73`.
-/

namespace BstLean.Part183

theorem TI_lite_19000 {n : ℕ} (hn : 19000 ≤ n) :
    BstLean.Part182.TI_hyp n (374 / 1000) (650 / 1000) (73 / 100) (1 / 10 ^ 18) :=
  BstLean.Part182.TI_hyp_mono BstLean.Part183.U.usn_lam le_rfl (BstLean.Part183.U.usn_TI hn)

end BstLean.Part183

open BstLean.Part183 in
#print axioms TI_lite_19000
