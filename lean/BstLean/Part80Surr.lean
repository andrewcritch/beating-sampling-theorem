import BstLean.Part80Defs
import BstLean.Part61Sur_Bias
import BstLean.Part56MomProg_Basic
import BstLean.Part50Laws

/-!
# Part 80: the surrogate interface `SurrRK`

For unit `v` and `0 ≤ t ≤ n`, the Taylor surrogate `surrRK n (KRK 1 n e) t v` and the true
distribution `lawRK n t v` are distributions on the sphere, and for every continuous `g`,
`(E_Q g − E_D g)² ≤ etaQ(e)² · Var_D g`. This is `Part61.surrogate_continuous_sq_bias61` at `C = 1`.
-/

namespace BstLean.Part80

open MeasureTheory
open BstLean.Part56 (UnitV lawRK surrRK KRK rk1)

theorem surrRK80 (n : ℕ) (hn : 2 ≤ n) (e : ℝ) (he : 0 < e) : SurrRK n e := by
  intro v hv t ht0 htn
  have hn1 : 1 ≤ n := by omega
  refine ⟨(BstLean.Part50.binghamA_antipodal hn1 (rk1 t v)).sph,
    BstLean.Part56.MomProg.surrRK_sphLaw hn1 _ t ht0 v, ?_⟩
  intro g hg
  exact BstLean.Part61.surrogate_continuous_sq_bias61 hn1 1 e t he ht0 (by simpa using htn) v hv g hg

end BstLean.Part80

#print axioms BstLean.Part80.surrRK80
