import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 13682–13688. -/
namespace BstLean.Part271.R3.Rows13682
open Real BstLean.Part130 BstLean.Part227

theorem width_13682 : mW 13682 = 299587405096233 := by
  have hu : mW 13682 ≤ 299587405096233 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13682 ≤ 299587405096232 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13682 : RowArithmetic 13682 (1134206790545227005171/1000000000000000000000000) (613020917184429340030373/1000000000000000000000000) (485381649763273/62500000000000000000000) where
  r0 := (624849779449/1000000000000000000)
  k0 := (747405982600759/200000000000000000)
  k6 := (11706466940158347/1000000000000000000)
  q := (165420675854017716561/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13682]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13682]

theorem width_13683 : mW 13683 = 299664049718245 := by
  have hu : mW 13683 ≤ 299664049718245 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13683 ≤ 299664049718244 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13683 : RowArithmetic 13683 (567086417955872333609/500000000000000000000000) (122601802024159672603761/200000000000000000000000) (3882313633065727/500000000000000000000000) where
  r0 := (156195320373/250000000000000000)
  k0 := (3736825075026419/1000000000000000000)
  k6 := (11706039158208663/1000000000000000000)
  q := (165426720937096495421/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13683]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13683]

theorem width_13684 : mW 13684 = 299740708345157 := by
  have hu : mW 13684 ≤ 299740708345157 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13684 ≤ 299740708345156 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13684 : RowArithmetic 13684 (283534722399436805513/250000000000000000000000) (306498552401622458469807/500000000000000000000000) (7763148529761977/1000000000000000000000000) where
  r0 := (624712796049/1000000000000000000)
  k0 := (373662026324527/100000000000000000)
  k6 := (11705611423152041/1000000000000000000)
  q := (82716382899640866731/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13684]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13684]

theorem width_13685 : mW 13685 = 299817380978506 := by
  have hu : mW 13685 ≤ 299817380978506 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13685 ≤ 299817380978505 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13685 : RowArithmetic 13685 (226820990320113120289/200000000000000000000000) (38311575076960003232509/62500000000000000000000) (7761670186969371/1000000000000000000000000) where
  r0 := (624644323117/1000000000000000000)
  k0 := (934103869413921/250000000000000000)
  k6 := (11705183734979913/1000000000000000000)
  q := (33087762088119528789/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13685]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13685]

theorem width_13686 : mW 13686 = 299894067619827 := by
  have hu : mW 13686 ≤ 299894067619827 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13686 ≤ 299894067619826 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13686 : RowArithmetic 13686 (1134071021917533169673/1000000000000000000000000) (612973299404734937447379/1000000000000000000000000) (388009611880959/50000000000000000000000) where
  r0 := (624575862693/1000000000000000000)
  k0 := (1868105359126497/500000000000000000)
  k6 := (2340951218736743/200000000000000000)
  q := (82722427430534217853/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13686]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13686]

theorem width_13687 : mW 13687 = 299970768270655 := by
  have hu : mW 13687 ≤ 299970768270655 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13687 ≤ 299970768270654 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13687 : RowArithmetic 13687 (113403710054598438439/100000000000000000000000) (306480699661480436913311/500000000000000000000000) (3879357340788503/500000000000000000000000) where
  r0 := (624507414773/1000000000000000000)
  k0 := (3736005985029541/1000000000000000000)
  k6 := (2926082124813721/250000000000000000)
  q := (165450899060718313161/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13687]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13687]

theorem width_13688 : mW 13688 = 300047482932525 := by
  have hu : mW 13688 ≤ 300047482932525 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13688 ≤ 300047482932524 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13688 : RowArithmetic 13688 (70875199217703424753/62500000000000000000000) (306474750492814638020503/500000000000000000000000) (7757237518708507/1000000000000000000000000) where
  r0 := (312219489677/500000000000000000)
  k0 := (233487579873791/62500000000000000)
  k6 := (5851950475842431/500000000000000000)
  q := (10341058939973217269/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13688]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13688]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 13682 then ⟨(1134206790545227005171/1000000000000000000000000), (613020917184429340030373/1000000000000000000000000), (485381649763273/62500000000000000000000)⟩ else
  if n = 13683 then ⟨(567086417955872333609/500000000000000000000000), (122601802024159672603761/200000000000000000000000), (3882313633065727/500000000000000000000000)⟩ else
  if n = 13684 then ⟨(283534722399436805513/250000000000000000000000), (306498552401622458469807/500000000000000000000000), (7763148529761977/1000000000000000000000000)⟩ else
  if n = 13685 then ⟨(226820990320113120289/200000000000000000000000), (38311575076960003232509/62500000000000000000000), (7761670186969371/1000000000000000000000000)⟩ else
  if n = 13686 then ⟨(1134071021917533169673/1000000000000000000000000), (612973299404734937447379/1000000000000000000000000), (388009611880959/50000000000000000000000)⟩ else
  if n = 13687 then ⟨(113403710054598438439/100000000000000000000000), (306480699661480436913311/500000000000000000000000), (3879357340788503/500000000000000000000000)⟩ else
  ⟨(70875199217703424753/62500000000000000000000), (306474750492814638020503/500000000000000000000000), (7757237518708507/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 13682 ≤ n) (hb : n ≤ 13688) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_13682
  · exact row_13683
  · exact row_13684
  · exact row_13685
  · exact row_13686
  · exact row_13687
  · exact row_13688

end BstLean.Part271.R3.Rows13682
