import BstLean.Part186FComb
import BstLean.Part186T7

/-!
# Part 186 (file `FPrv`): the frame junction at `n ≥ 16 500`, unconditional

No proof is left open; no `native_decide` or `axiom` is used. `FREE165_of_TI` (file `FComb`) with
Lemma TI discharged by `TI_two_16384` (`λ = 0.647` on `[0.370, 0.655]`, every `n ≥ 16 384`).
-/

namespace BstLean.Part186

/-- **The frame junction at `n ≥ 16 500`** (unconditional): `FREEg_stmt 16500 (−0.002691)`. -/
theorem FREE165_proved : BstLean.Part183.FREEg_stmt 16500 roomT165 :=
  BstLean.Part183.F165.FREE165_of_TI fun n hn => TI_two_16384 n (le_trans (by norm_num) hn)

end BstLean.Part186

#print axioms BstLean.Part186.FREE165_proved
