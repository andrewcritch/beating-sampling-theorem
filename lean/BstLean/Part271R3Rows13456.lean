import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 13456–13456. -/
namespace BstLean.Part271.R3.Rows13456
open Real BstLean.Part130 BstLean.Part227

theorem width_13456 : mW 13456 = 282621973446656 := by
  have hu : mW 13456 ≤ 282621973446656 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13456 ≤ 282621973446655 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13456 : RowArithmetic 13456 (1142099262454895036477/1000000000000000000000000) (307878757193662500548351/500000000000000000000000) (253461173070859/31250000000000000000000) where
  r0 := (320328836771/500000000000000000)
  k0 := (189200284114901/50000000000000000)
  k6 := (46110802591693/3906250000000000)
  q := (164048773235279025661/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13456]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13456]

noncomputable def record (n : ℕ) : Allowances :=
  ⟨(1142099262454895036477/1000000000000000000000000), (307878757193662500548351/500000000000000000000000), (253461173070859/31250000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 13456 ≤ n) (hb : n ≤ 13456) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_13456

end BstLean.Part271.R3.Rows13456
