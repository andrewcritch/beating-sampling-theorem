import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15129–15129. -/
namespace BstLean.Part271.R3.Rows15129
open Real BstLean.Part130 BstLean.Part227

theorem width_15129 : mW 15129 = 425927596977747 := by
  have hu : mW 15129 ≤ 425927596977747 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15129 ≤ 425927596977746 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15129 : RowArithmetic 15129 (273150713576180266231/250000000000000000000000) (298716702054513483466311/500000000000000000000000) (5978840741069467/1000000000000000000000000) where
  r0 := (537383918357/1000000000000000000)
  k0 := (138624849577723/40000000000000000)
  k6 := (2783143076753893/250000000000000000)
  q := (173948268171890691003/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15129]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15129]

noncomputable def record (n : ℕ) : Allowances :=
  ⟨(273150713576180266231/250000000000000000000000), (298716702054513483466311/500000000000000000000000), (5978840741069467/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15129 ≤ n) (hb : n ≤ 15129) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15129

end BstLean.Part271.R3.Rows15129
