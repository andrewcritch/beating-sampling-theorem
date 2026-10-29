import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 13451–13455. -/
namespace BstLean.Part271.R3.Rows13451
open Real BstLean.Part130 BstLean.Part227

theorem width_13451 : mW 13451 = 282254584347859 := by
  have hu : mW 13451 ≤ 282254584347859 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13451 ≤ 282254584347858 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13451 : RowArithmetic 13451 (1142278923763553321423/1000000000000000000000000) (6158191041792680445921/10000000000000000000000) (8118622287539197/1000000000000000000000000) where
  r0 := (641014924233/1000000000000000000)
  k0 := (118283142969527/31250000000000000)
  k6 := (1180655921648227/100000000000000000)
  q := (82009145831425411817/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13451]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13451]

theorem width_13452 : mW 13452 = 282328034861073 := by
  have hu : mW 13452 ≤ 282328034861073 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13452 ≤ 282328034861072 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13452 : RowArithmetic 13452 (571121486788667118303/500000000000000000000000) (615806782533403116759889/1000000000000000000000000) (324681939411377/40000000000000000000000) where
  r0 := (640943447537/1000000000000000000)
  k0 := (3784849541587083/1000000000000000000)
  k6 := (5903060184017139/500000000000000000)
  q := (82012194215250697681/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13452]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13452]

theorem width_13453 : mW 13453 = 282401499026037 := by
  have hu : mW 13453 ≤ 282401499026037 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13453 ≤ 282401499026036 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13453 : RowArithmetic 13453 (285551758089071140503/250000000000000000000000) (307897231365858512168001/500000000000000000000000) (81154751093781/10000000000000000000000) where
  r0 := (640871984123/1000000000000000000)
  k0 := (473079816950009/125000000000000000)
  k6 := (11805681568518487/1000000000000000000)
  q := (41007621242886059411/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13453]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13453]

theorem width_13454 : mW 13454 = 282474976844275 := by
  have hu : mW 13454 ≤ 282474976844275 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13454 ≤ 282474976844274 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13454 : RowArithmetic 13454 (571085550048738515413/500000000000000000000000) (1539455361934422591873/2500000000000000000000) (101423776995899/12500000000000000000000) where
  r0 := (160200133497/250000000000000000)
  k0 := (1892213778529781/500000000000000000)
  k6 := (2361048563585161/200000000000000000)
  q := (41009145321501154153/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13454]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13454]

theorem width_13455 : mW 13455 = 282548468317307 := by
  have hu : mW 13455 ≤ 282548468317307 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13455 ≤ 282548468317306 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13455 : RowArithmetic 13455 (1142135176797988551211/1000000000000000000000000) (307884914329559255730129/500000000000000000000000) (2028082409004441/250000000000000000000000) where
  r0 := (640729097129/1000000000000000000)
  k0 := (1892108302980643/500000000000000000)
  k6 := (11804804116247141/1000000000000000000)
  q := (164042677373907793703/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13455]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13455]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 13451 then ⟨(1142278923763553321423/1000000000000000000000000), (6158191041792680445921/10000000000000000000000), (8118622287539197/1000000000000000000000000)⟩ else
  if n = 13452 then ⟨(571121486788667118303/500000000000000000000000), (615806782533403116759889/1000000000000000000000000), (324681939411377/40000000000000000000000)⟩ else
  if n = 13453 then ⟨(285551758089071140503/250000000000000000000000), (307897231365858512168001/500000000000000000000000), (81154751093781/10000000000000000000000)⟩ else
  if n = 13454 then ⟨(571085550048738515413/500000000000000000000000), (1539455361934422591873/2500000000000000000000), (101423776995899/12500000000000000000000)⟩ else
  ⟨(1142135176797988551211/1000000000000000000000000), (307884914329559255730129/500000000000000000000000), (2028082409004441/250000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 13451 ≤ n) (hb : n ≤ 13455) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_13451
  · exact row_13452
  · exact row_13453
  · exact row_13454
  · exact row_13455

end BstLean.Part271.R3.Rows13451
