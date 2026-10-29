import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 13225–13225. -/
namespace BstLean.Part271.R3.Rows13225
open Real BstLean.Part130 BstLean.Part227

theorem width_13225 : mW 13225 = 266001988046875 := by
  have hu : mW 13225 ≤ 266001988046875 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13225 ≤ 266001988046874 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13225 : RowArithmetic 13225 (575319735108836514491/500000000000000000000000) (618651976856958765135021/1000000000000000000000000) (8485534062783457/1000000000000000000000000) where
  r0 := (41094764527/62500000000000000)
  k0 := (239591838756359/62500000000000000)
  k6 := (476280484787101/40000000000000000)
  q := (162634559672905930613/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13225]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13225]

noncomputable def record (n : ℕ) : Allowances :=
  ⟨(575319735108836514491/500000000000000000000000), (618651976856958765135021/1000000000000000000000000), (8485534062783457/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 13225) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_13225

end BstLean.Part271.R3.Rows13225
