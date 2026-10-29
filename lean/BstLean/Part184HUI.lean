import BstLean.Part184HSNum
import BstLean.Part184HComb
import BstLean.Part182TImono

/-!
# Part 184 (file `HUI`): Lemma TI ("TI-lite") for every `n ≥ 17 750` and the frame junction
`FREE1775_stmt` with NO hypothesis

No proof is left open; no `native_decide` or `axiom` is used.

* **`TI_lite_17750`**: `TI_hyp n 0.374 0.65 0.735 10⁻¹⁸` for every `n ≥ 17 750`, from Part 182's
  assembly `ta_TI46` with the numerics of files `HENum`, `HSNum` (`k_E = 0.73`, `k_o = 0.028`,
  `k_s = 0.182`, `η = 271/10⁶`): `λ = ta_lam(0.73, 0.028, 0.182) ≈ 0.7315 ≤ 0.735`.
* **`FREE1775_proved : FREEg_stmt 17750 (−0.0016)`** (= `FREE1775_stmt`): the frame junction at `n ≥ 17 750` with the room
  `roomA + roomX + roomT1775`, `roomT1775 = −0.0016` (file `HComb`: frame `2.205/n`, tails `≤ 0.00459`,
  budget `0.005409`).
-/

namespace BstLean.Part184

theorem TI_lite_17750 {n : ℕ} (hn : 17750 ≤ n) :
    BstLean.Part182.TI_hyp n (374 / 1000) (650 / 1000) (735 / 1000) (1 / 10 ^ 18) :=
  BstLean.Part182.TI_hyp_mono BstLean.Part184.HT.fsn_lam le_rfl (BstLean.Part184.HT.fsn_TI hn)

/-- **The frame junction at `n ≥ 17 750`, with no hypothesis.** -/
theorem FREE1775_proved : BstLean.Part183.FREEg_stmt 17750 (-(16 / 10000)) :=
  BstLean.Part183.F1775.FREE1775_of_TI (fun _ hn => TI_lite_17750 hn)

end BstLean.Part184

open BstLean.Part184 in
#print axioms TI_lite_17750
open BstLean.Part184 in
#print axioms FREE1775_proved
