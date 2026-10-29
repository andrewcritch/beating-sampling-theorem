import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14400–14400. -/
namespace BstLean.Part271.R3.Rows14400
open Real BstLean.Part130 BstLean.Part227

theorem width_14400 : mW 14400 = 358318080000000 := by
  have hu : mW 14400 ≤ 358318080000000 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14400 ≤ 358318079999999 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14400 : RowArithmetic 14400 (1111815794516512966947/1000000000000000000000000) (302448664815488013637001/500000000000000000000000) (6797744766760547/1000000000000000000000000) where
  r0 := (72337962963/125000000000000000)
  k0 := (449548867230117/125000000000000000)
  k6 := (11410886614690961/1000000000000000000)
  q := (169705627484771405857/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14400]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14400]

noncomputable def record (n : ℕ) : Allowances :=
  ⟨(1111815794516512966947/1000000000000000000000000), (302448664815488013637001/500000000000000000000000), (6797744766760547/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14400 ≤ n) (hb : n ≤ 14400) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14400

end BstLean.Part271.R3.Rows14400
