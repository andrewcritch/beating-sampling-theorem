import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14884–14884. -/
namespace BstLean.Part271.R3.Rows14884
open Real BstLean.Part130 BstLean.Part227

theorem width_14884 : mW 14884 = 402271083010688 := by
  have hu : mW 14884 ≤ 402271083010688 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14884 ≤ 402271083010687 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14884 : RowArithmetic 14884 (43948407684908082779/40000000000000000000000) (299930612482457927537609/500000000000000000000000) (6237874573118929/1000000000000000000000000) where
  r0 := (550706887361/1000000000000000000)
  k0 := (1754159266751337/500000000000000000)
  k6 := (11223822899696027/1000000000000000000)
  q := (86267027304758797977/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14884]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14884]

noncomputable def record (n : ℕ) : Allowances :=
  ⟨(43948407684908082779/40000000000000000000000), (299930612482457927537609/500000000000000000000000), (6237874573118929/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14884 ≤ n) (hb : n ≤ 14884) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14884

end BstLean.Part271.R3.Rows14884
