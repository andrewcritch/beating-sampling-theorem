import BstLean.Part182SNum
import BstLean.Part182TImono

/-!
# Part 182 (file `TI`): Lemma TI ("TI-lite") PROVED for every `n ≥ 21 000`

No proof is left open; no `native_decide` or `axiom` is used.

**`TI_lite_proved`**: `TI_hyp n 0.383 0.641 0.72 10⁻¹⁸` for every `n ≥ 21 000`: for every fixed
pair of unit inputs with `0.383 ≤ x·x' ≤ 0.641`, `Pr_{A₁,A₂}(‖(𝒥(x)Π_x)ᵀ𝒥(x')Π_{x'}‖ > 0.72·n) ≤ 10⁻¹⁸`.
Assembly `ta_TI46` (file `TIA`: E, O, S blocks + mode separation, 51 e^{−τ} + 12 e^{−2η²m} tails,
τ = 46, η = 23/100000) with the numerics `en_kE` (`k_E = 0.715`), `sn_ko` (`k_o = 0.026`),
`sn_S` (`k_s = 0.18`): `λ = ta_lam(0.715, 0.026, 0.18) ≈ 0.7163 ≤ 0.72`. The paper's Lemma TI has
`λ ≈ 0.585` at 21 000; Lean's form uses only UPPER singular-value bounds (no Davidson–Szarek).
-/

namespace BstLean.Part182

theorem TI_lite_proved {n : ℕ} (hn : 21000 ≤ n) :
    TI_hyp n (383 / 1000) (641 / 1000) (72 / 100) (1 / 10 ^ 18) :=
  TI_hyp_mono sn_lam le_rfl (sn_TI hn)

end BstLean.Part182

open BstLean.Part182 in
#print axioms TI_lite_proved
