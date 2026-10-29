import BstLean.Part185All

/-!
# Part 186 (file `Def`): the interface of Part 186

No proof is left open; no `native_decide` or `axiom` is used.

* `BiasRA_stmt`: the row-averaged bias moments (paper Lemma `t7:p08:RA`, eighth-moment form):
  on the statistics event of the chain (thresholds `S₋ = 1/(5n)`, `S₊ = 5/n`, `D_m = H_m = 16/n³`,
  `V_m = 64/n⁴`, `P_m = 68/n⁴`), `BiasMomF (O₁) Gb (194/n)` and `BiasMomW (O₁) Gb (148/n)`
  for every `n ≥ 16 384`. Part 185 has `270/n` and `280/n` (row bounds in `L⁸`); the row
  averaging pays the radial factors in `L²` (location) and `L¹` (energy).
-/

namespace BstLean.Part186

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171

/-- **The row-averaged bias moments** (statement). -/
def BiasRA_stmt : Prop :=
  ∀ {n : ℕ}, 16384 ≤ n → ∀ {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)},
    Gb ⊆ StatEv n (SminN n) (SmaxN n) (DmN n) (DmN n) (VmN n) (68 * PmN n) →
    BstLean.Part170.BiasMomF (O1n n) Gb (194 / n) ∧ BstLean.Part170.BiasMomW (O1n n) Gb (148 / n)

end BstLean.Part186
