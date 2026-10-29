import BstLean.Part184ISNum
import BstLean.Part184IComb
import BstLean.Part182TImono

/-!
# Part 184 (file `IUI`): Lemma TI ("TI-lite") for every `n ≥ 17 500` and the frame junction
`FREE175_stmt` with NO hypothesis

No proof is left open; no `native_decide` or `axiom` is used.

* **`TI_lite_17500`**: `TI_hyp n 0.374 0.65 0.735 10⁻¹⁸` for every `n ≥ 17 500`, from Part 182's
  assembly `ta_TI46` with the numerics of files `IENum`, `ISNum` (`k_E = 0.73`, `k_o = 0.028`,
  `k_s = 0.182`, `η = 275/10⁶`): `λ = ta_lam(0.73, 0.028, 0.182) ≈ 0.7315 ≤ 0.735`.
* **`FREE175_proved : FREEg_stmt 17500 (−0.0020)`** (= `FREE175_stmt`): the frame junction at `n ≥ 17 500` with the room
  `roomA + roomX + roomT175`, `roomT175 = −0.0020` (file `IComb`: frame `2.211/n`, tails `≤ 0.005041`,
  budget `0.004958`).
-/

namespace BstLean.Part184

theorem TI_lite_17500 {n : ℕ} (hn : 17500 ≤ n) :
    BstLean.Part182.TI_hyp n (374 / 1000) (650 / 1000) (735 / 1000) (1 / 10 ^ 18) :=
  BstLean.Part182.TI_hyp_mono BstLean.Part184.IT.fsn_lam le_rfl (BstLean.Part184.IT.fsn_TI hn)

/-- **The frame junction at `n ≥ 17 500`, with no hypothesis.** -/
theorem FREE175_proved : BstLean.Part183.FREEg_stmt 17500 (-(20 / 10000)) :=
  BstLean.Part183.F175.FREE175_of_TI (fun _ hn => TI_lite_17500 hn)

end BstLean.Part184

open BstLean.Part184 in
#print axioms TI_lite_17500
open BstLean.Part184 in
#print axioms FREE175_proved
