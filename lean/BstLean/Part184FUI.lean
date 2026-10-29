import BstLean.Part184FSNum
import BstLean.Part184FComb
import BstLean.Part182TImono

/-!
# Part 184 (file `FUI`): Lemma TI ("TI-lite") for every `n ≥ 18 500` and the frame junction
`FREE185_stmt` with NO hypothesis

No proof is left open; no `native_decide` or `axiom` is used.

* **`TI_lite_18500`**: `TI_hyp n 0.374 0.65 0.735 10⁻¹⁸` for every `n ≥ 18 500`, from Part 182's
  assembly `ta_TI46` with the numerics of files `FENum`, `FSNum` (`k_E = 0.73`, `k_o = 0.027`,
  `k_s = 0.182`, `η = 260/10⁶`): `λ = ta_lam(0.73, 0.027, 0.182) ≈ 0.7314 ≤ 0.735`.
* **`FREE185_proved : FREE185_stmt`**: the frame junction at `n ≥ 18 500` with the room
  `roomA + roomX + roomT185`, `roomT185 = −0.0007` (file `FComb`: frame `2.19/n`, tails `≤ 0.0035`,
  budget `0.006499`).
-/

namespace BstLean.Part184

theorem TI_lite_18500 {n : ℕ} (hn : 18500 ≤ n) :
    BstLean.Part182.TI_hyp n (374 / 1000) (650 / 1000) (735 / 1000) (1 / 10 ^ 18) :=
  BstLean.Part182.TI_hyp_mono BstLean.Part184.FT.fsn_lam le_rfl (BstLean.Part184.FT.fsn_TI hn)

/-- **The frame junction at `n ≥ 18 500`, with no hypothesis.** -/
theorem FREE185_proved : FREE185_stmt :=
  BstLean.Part183.F185.FREE185_of_TI (fun _ hn => TI_lite_18500 hn)

end BstLean.Part184

open BstLean.Part184 in
#print axioms TI_lite_18500
open BstLean.Part184 in
#print axioms FREE185_proved
