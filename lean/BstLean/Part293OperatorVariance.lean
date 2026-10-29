import BstLean.Part172SBnd
import BstLean.Part278Good

/-! The paid first-operator event also supplies the upper node variance. -/
namespace BstLean.Part293
open Real BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part172

theorem variance_le_operator {n : ℕ} (hn : 2 ≤ n) (c : Ret n)
    (hc : c.1.2 ≠ 0) {O s : ℝ} (hO : OpB (A1 c) O) (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ 2 * O ^ 2 / ((n : ℝ) * (n - 1)) * (1 - s ^ 2) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hq : 0 ≤ 1 - s ^ 2 := by linarith
  have hsum : (∑ i, (normSq (A1 c i) - sg_z (uHat c) (A1 c i) ^ 2)) ≤
      (n : ℝ) * O ^ 2 := by
    apply le_trans (Finset.sum_le_sum fun i _ => sub_le_self _ (sq_nonneg _))
    exact BstLean.Part278.frob_le c hO
  apply (sg_vsig2_upper hn c hc hs).trans
  apply le_trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  apply le_of_eq
  simp only [mA, Nat.cast_pow, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  field_simp <;> ring

end BstLean.Part293

/-- info: 'BstLean.Part293.variance_le_operator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.variance_le_operator
