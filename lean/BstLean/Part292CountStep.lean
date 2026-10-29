import BstLean.Part292CountP24

/-! Explicit indices avoid reducing recursive counts when checking numerical index equalities. -/
namespace BstLean.Part292
open BstLean.Part239

theorem count_step_checked (p p1 p2 k k1 a b v : ℕ)
    (hp : p = p2+2) (hp1 : p1 = p2+1) (hk : k = k1+1)
    (h1 : noSingleton p1 k = a) (h2 : noSingleton p2 k1 = b)
    (hv : k*a+p1*b=v) : noSingleton p k = v := by
  rw [hp, hk, noSingleton_recurrence, ← hp1, ← hk, h1, h2]
  exact hv

theorem count_zero_checked (p p1 : ℕ) (hp : p = p1+1) : noSingleton p 0 = 0 := by
  rw [hp]
  exact noSingleton_zero_column p1

end BstLean.Part292
