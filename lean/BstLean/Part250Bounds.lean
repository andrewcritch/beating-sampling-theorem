import BstLean.Part227Direct
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part228Arithmetic

/-! Exact width and elementary bounds for the World row. -/
namespace BstLean.Part250
open Real BstLean.Part130 BstLean.Part140 BstLean.Part227
open BstLean.Part228

noncomputable def rowEps : Fin 4 → ℝ := ![1/10^5, 1/1000, 1/1000, 3]

theorem bounds_div {x y l u a b L U : ℝ}
    (hx : Bounds x l u) (hy : Bounds (1/y) a b)
    (h : L ≤ l*a ∧ L ≤ l*b ∧ L ≤ u*a ∧ L ≤ u*b ∧
      l*a ≤ U ∧ l*b ≤ U ∧ u*a ≤ U ∧ u*b ≤ U) : Bounds (x/y) L U := by
  simpa only [div_eq_mul_inv, one_mul] using Bounds.mul hx hy h

theorem width : mW 12225 = 202009148155087 := by
  have hu : mW 12225 ≤ 202009148155087 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12225 ≤ 202009148155086 := by rw [mW_le_iff]; norm_num
  omega

theorem pi_bounds : Bounds π (314159265358979323846 / 10^20)
    (314159265358979323847 / 10^20) := by
  constructor
  · convert pi_gt_d20.le using 1 <;> norm_num
  · convert pi_lt_d20.le using 1 <;> norm_num

theorem kap_bounds : Bounds (kap1 (2*12225)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24450 ^ 2)
    (6509404625435392055971823/1000000000000000000000000000000)
    (65096708696427394072975451/10000000000000000000000000000000) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24450) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

end BstLean.Part250
