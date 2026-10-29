import BstLean.Part184GSNum
import BstLean.Part184GComb
import BstLean.Part182TImono

/-!
# Part 184 (file `GUI`): Lemma TI ("TI-lite") for every `n ≥ 18 000` and the frame junction
`FREE18_stmt` with NO hypothesis

No proof is left open; no `native_decide` or `axiom` is used.

* **`TI_lite_18000`**: `TI_hyp n 0.374 0.65 0.735 10⁻¹⁸` for every `n ≥ 18 000`, from Part 182's
  assembly `ta_TI46` with the numerics of files `GENum`, `GSNum` (`k_E = 0.73`, `k_o = 0.028`,
  `k_s = 0.182`, `η = 267/10⁶`): `λ = ta_lam(0.73, 0.028, 0.182) ≈ 0.7315 ≤ 0.735`.
* **`FREE18_proved : FREE18_stmt`**: the frame junction at `n ≥ 18 000` with the room
  `roomA + roomX + roomT18`, `roomT18 = −0.0012` (file `GComb`: frame `2.20/n`, tails `≤ 0.00417`,
  budget `0.005829`).
-/

namespace BstLean.Part184

theorem TI_lite_18000 {n : ℕ} (hn : 18000 ≤ n) :
    BstLean.Part182.TI_hyp n (374 / 1000) (650 / 1000) (735 / 1000) (1 / 10 ^ 18) :=
  BstLean.Part182.TI_hyp_mono BstLean.Part184.GT.fsn_lam le_rfl (BstLean.Part184.GT.fsn_TI hn)

/-- **The frame junction at `n ≥ 18 000`, with no hypothesis.** -/
theorem FREE18_proved : FREE18_stmt :=
  BstLean.Part183.F18.FREE18_of_TI (fun _ hn => TI_lite_18000 hn)

end BstLean.Part184

open BstLean.Part184 in
#print axioms TI_lite_18000
open BstLean.Part184 in
#print axioms FREE18_proved
