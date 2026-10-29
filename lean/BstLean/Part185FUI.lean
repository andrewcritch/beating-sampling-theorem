import BstLean.Part185FSNum
import BstLean.Part185FComb
import BstLean.Part182TImono

/-!
# Part 185 (file `FUI`): Lemma TI ("TI-lite") for every `n ≥ 17 250` and the frame junction
`FREE1725_stmt` with NO hypothesis

No proof is left open; no `native_decide` or `axiom` is used.

* **`TI_lite_17250`**: `TI_hyp n 0.374 0.65 0.735 10⁻¹⁸` for every `n ≥ 17 250`, from Part 182's
  assembly `ta_TI46` with the numerics of files `FENum`, `FSNum` (`k_E = 0.73`, `k_o = 0.0281`,
  `k_s = 0.182`, `η = 279/10⁶`): `λ = ta_lam(0.73, 0.0281, 0.182) ≈ 0.7314 ≤ 0.735`.
* **`FREE1725_proved : FREEg_stmt 17250 (−0.002503)`** (= `FREE1725_stmt`): the frame junction at
  `n ≥ 17 250` with the room `roomA + roomX + roomT1725`, `roomT1725 = −0.002503` (file `FComb`:
  frame `2.217/n`, tails `≤ 0.005546`, budget `0.004453`).
-/

namespace BstLean.Part185

theorem TI_lite_17250 {n : ℕ} (hn : 17250 ≤ n) :
    BstLean.Part182.TI_hyp n (374 / 1000) (650 / 1000) (735 / 1000) (1 / 10 ^ 18) :=
  BstLean.Part182.TI_hyp_mono BstLean.Part185.FT.fsn_lam le_rfl (BstLean.Part185.FT.fsn_TI hn)

/-- **The frame junction at `n ≥ 17 250`, with no hypothesis.** -/
theorem FREE1725_proved : BstLean.Part183.FREEg_stmt 17250 (-(2503 / 1000000)) :=
  BstLean.Part183.F1725.FREE1725_of_TI (fun _ hn => TI_lite_17250 hn)

end BstLean.Part185

open BstLean.Part185 in
#print axioms TI_lite_17250
open BstLean.Part185 in
#print axioms FREE1725_proved
