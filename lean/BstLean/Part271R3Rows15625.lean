import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15625–15625. -/
namespace BstLean.Part271.R3.Rows15625
open Real BstLean.Part130 BstLean.Part227

theorem width_15625 : mW 15625 = 476837158203125 := by
  have hu : mW 15625 ≤ 476837158203125 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15625 ≤ 476837158203124 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15625 : RowArithmetic 15625 (540600375508606146759/500000000000000000000000) (148186918767506925503873/250000000000000000000000) (27493016767913/5000000000000000000000) where
  r0 := (1/1953125)
  k0 := (845694980474639/250000000000000000)
  k6 := (10954451150103323/1000000000000000000)
  q := (176776695296636881101/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15625]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15625]

noncomputable def record (n : ℕ) : Allowances :=
  ⟨(540600375508606146759/500000000000000000000000), (148186918767506925503873/250000000000000000000000), (27493016767913/5000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15625 ≤ n) (hb : n ≤ 15625) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15625

end BstLean.Part271.R3.Rows15625
