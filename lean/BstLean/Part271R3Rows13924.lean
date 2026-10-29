import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 13924–13924. -/
namespace BstLean.Part271.R3.Rows13924
open Real BstLean.Part130 BstLean.Part227

theorem width_13924 : mW 13924 = 318547390056832 := by
  have hu : mW 13924 ≤ 318547390056832 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13924 ≤ 318547390056831 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13924 : RowArithmetic 13924 (1126226293808372070997/1000000000000000000000000) (610189389046034193506919/1000000000000000000000000) (7419331751359779/1000000000000000000000000) where
  r0 := (15215771817/25000000000000000)
  k0 := (3688210949010103/1000000000000000000)
  k6 := (11604291472567079/1000000000000000000)
  q := (166877200360025215759/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13924]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13924]

noncomputable def record (n : ℕ) : Allowances :=
  ⟨(1126226293808372070997/1000000000000000000000000), (610189389046034193506919/1000000000000000000000000), (7419331751359779/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 13924 ≤ n) (hb : n ≤ 13924) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_13924

end BstLean.Part271.R3.Rows13924
