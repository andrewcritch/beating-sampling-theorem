import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 13689–13689. -/
namespace BstLean.Part271.R3.Rows13689
open Real BstLean.Part130 BstLean.Part227

theorem width_13689 : mW 13689 = 300124211606973 := by
  have hu : mW 13689 ≤ 300124211606973 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13689 ≤ 300124211606972 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13689 : RowArithmetic 13689 (226793856545336076007/200000000000000000000000) (612937604392331738434791/1000000000000000000000000) (12409217198207/1600000000000000000000) where
  r0 := (624370556433/1000000000000000000)
  k0 := (3735596597101667/1000000000000000000)
  k6 := (365733545342659/31250000000000000)
  q := (16546298679765212071/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13689]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13689]

noncomputable def record (n : ℕ) : Allowances :=
  ⟨(226793856545336076007/200000000000000000000000), (612937604392331738434791/1000000000000000000000000), (12409217198207/1600000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 13689 ≤ n) (hb : n ≤ 13689) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_13689

end BstLean.Part271.R3.Rows13689
