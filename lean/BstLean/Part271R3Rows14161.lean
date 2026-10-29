import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14161–14161. -/
namespace BstLean.Part271.R3.Rows14161
open Real BstLean.Part130 BstLean.Part227

theorem width_14161 : mW 14161 = 337931541778439 := by
  have hu : mW 14161 ≤ 337931541778439 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14161 ≤ 337931541778438 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14161 : RowArithmetic 14161 (559424285865282154917/500000000000000000000000) (121502031214872828039861/200000000000000000000000) (3550171499132251/500000000000000000000000) where
  r0 := (18544244193/31250000000000000)
  k0 := (1820909350217193/500000000000000000)
  k6 := (11506776418175759/1000000000000000000)
  q := (21036426740299788851/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14161]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14161]

noncomputable def record (n : ℕ) : Allowances :=
  ⟨(559424285865282154917/500000000000000000000000), (121502031214872828039861/200000000000000000000000), (3550171499132251/500000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14161 ≤ n) (hb : n ≤ 14161) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14161

end BstLean.Part271.R3.Rows14161
