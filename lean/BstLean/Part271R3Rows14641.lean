import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14641–14641. -/
namespace BstLean.Part271.R3.Rows14641
open Real BstLean.Part130 BstLean.Part227

theorem width_14641 : mW 14641 = 379749833583241 := by
  have hu : mW 14641 ≤ 379749833583241 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14641 ≤ 379749833583240 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14641 : RowArithmetic 14641 (276277235007915842013/250000000000000000000000) (602348461842101024596857/1000000000000000000000000) (1627639788037741/250000000000000000000000) where
  r0 := (282236965027/500000000000000000)
  k0 := (443987477594859/125000000000000000)
  k6 := (707286360414729/62500000000000000)
  q := (85559920523572250453/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14641]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14641]

noncomputable def record (n : ℕ) : Allowances :=
  ⟨(276277235007915842013/250000000000000000000000), (602348461842101024596857/1000000000000000000000000), (1627639788037741/250000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14641 ≤ n) (hb : n ≤ 14641) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14641

end BstLean.Part271.R3.Rows14641
