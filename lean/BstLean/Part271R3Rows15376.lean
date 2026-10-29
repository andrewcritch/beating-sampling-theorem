import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15376–15376. -/
namespace BstLean.Part271.R3.Rows15376
open Real BstLean.Part130 BstLean.Part227

theorem width_15376 : mW 15376 = 450766669594624 := by
  have hu : mW 15376 ≤ 450766669594624 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15376 ≤ 450766669594623 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15376 : RowArithmetic 15376 (1086771270327564069493/1000000000000000000000000) (119012578095050837749741/200000000000000000000000) (716583006343319/125000000000000000000000) where
  r0 := (262243630627/500000000000000000)
  k0 := (3423783037668553/1000000000000000000)
  k6 := (11042793498088027/1000000000000000000)
  q := (43840620433565946513/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15376]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15376]

noncomputable def record (n : ℕ) : Allowances :=
  ⟨(1086771270327564069493/1000000000000000000000000), (119012578095050837749741/200000000000000000000000), (716583006343319/125000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15376 ≤ n) (hb : n ≤ 15376) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15376

end BstLean.Part271.R3.Rows15376
