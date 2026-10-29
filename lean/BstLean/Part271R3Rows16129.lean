import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 16129–16129. -/
namespace BstLean.Part271.R3.Rows16129
open Real BstLean.Part130 BstLean.Part227

theorem width_16129 : mW 16129 = 532875860165503 := by
  have hu : mW 16129 ≤ 532875860165503 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16129 ≤ 532875860165502 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16129 : RowArithmetic 16129 (535394292868866776767/500000000000000000000000) (58827556731431700220673/100000000000000000000000) (253205233637597/50000000000000000000000) where
  r0 := (244094976379/500000000000000000)
  k0 := (3303187164564143/1000000000000000000)
  k6 := (2695485027092353/250000000000000000)
  q := (89802561210691535599/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16129]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16129]

noncomputable def record (n : ℕ) : Allowances :=
  ⟨(535394292868866776767/500000000000000000000000), (58827556731431700220673/100000000000000000000000), (253205233637597/50000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 16129 ≤ n) (hb : n ≤ 16129) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_16129

end BstLean.Part271.R3.Rows16129
