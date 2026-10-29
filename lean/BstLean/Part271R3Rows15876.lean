import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15876–15876. -/
namespace BstLean.Part271.R3.Rows15876
open Real BstLean.Part130 BstLean.Part227

theorem width_15876 : mW 15876 = 504189521813376 := by
  have hu : mW 15876 ≤ 504189521813376 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15876 ≤ 504189521813375 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15876 : RowArithmetic 15876 (107587750684604322711/100000000000000000000000) (590485842857435230100181/1000000000000000000000000) (5152310624079/976562500000000000000) where
  r0 := (499906017669/1000000000000000000)
  k0 := (3342588741514899/1000000000000000000)
  k6 := (10867511061610439/1000000000000000000)
  q := (3563818177180199523/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15876]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15876]

noncomputable def record (n : ℕ) : Allowances :=
  ⟨(107587750684604322711/100000000000000000000000), (590485842857435230100181/1000000000000000000000000), (5152310624079/976562500000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15876 ≤ n) (hb : n ≤ 15876) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15876

end BstLean.Part271.R3.Rows15876
