import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14626–14640. -/
namespace BstLean.Part271.R3.Rows14626
open Real BstLean.Part130 BstLean.Part227

theorem width_14626 : mW 14626 = 378389861778842 := by
  have hu : mW 14626 ≤ 378389861778842 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14626 ≤ 378389861778841 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14626 : RowArithmetic 14626 (138189453001469732049/125000000000000000000000) (602504674531471045990411/1000000000000000000000000) (1305586750046841/200000000000000000000000) where
  r0 := (282671257357/500000000000000000)
  k0 := (28437052115979/8000000000000000)
  k6 := (566119162901837/50000000000000000)
  q := (85516080359193264419/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14626]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14626]

theorem width_14627 : mW 14627 = 378480418165134 := by
  have hu : mW 14627 ≤ 378480418165134 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14627 ≤ 378480418165133 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14627 : RowArithmetic 14627 (1105488468334773355259/1000000000000000000000000) (602494250479063945522783/1000000000000000000000000) (6526773428448507/1000000000000000000000000) where
  r0 := (113056907957/200000000000000000)
  k0 := (888612312266813/250000000000000000)
  k6 := (5660998107161817/500000000000000000)
  q := (17103800747202359759/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14627]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14627]

theorem width_14628 : mW 14628 = 378570990030356 := by
  have hu : mW 14628 ≤ 378570990030356 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14628 ≤ 378570990030355 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14628 : RowArithmetic 14628 (552730659433749479201/500000000000000000000000) (602483827838424884034457/1000000000000000000000000) (6525613394953243/1000000000000000000000000) where
  r0 := (113045314953/200000000000000000)
  k0 := (222141687840337/62500000000000000)
  k6 := (707600575643741/62500000000000000)
  q := (85521927012901200179/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14628]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14628]

theorem width_14629 : mW 14629 = 378661577376096 := by
  have hu : mW 14629 ≤ 378661577376096 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14629 ≤ 378661577376095 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14629 : RowArithmetic 14629 (1105434175608075464823/1000000000000000000000000) (60247340660924828741139/100000000000000000000000) (6524453649656443/1000000000000000000000000) where
  r0 := (11303372393/20000000000000000)
  k0 := (888521195905643/250000000000000000)
  k6 := (11321222245958623/1000000000000000000)
  q := (85524850189871715437/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14629]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14629]

theorem width_14630 : mW 14630 = 378752180203941 := by
  have hu : mW 14630 ≤ 378752180203941 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14630 ≤ 378752180203940 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14630 : RowArithmetic 14630 (552703519277322419469/500000000000000000000000) (60246298679122871884239/100000000000000000000000) (652329419246619/100000000000000000000000) where
  r0 := (565110674439/1000000000000000000)
  k0 := (3553902583599001/1000000000000000000)
  k6 := (2264167064258631/200000000000000000)
  q := (42763886633466794841/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14630]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14630]

theorem width_14631 : mW 14631 = 378842798515479 := by
  have hu : mW 14631 ≤ 378842798515479 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14631 ≤ 378842798515478 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14631 : RowArithmetic 14631 (552689953852674651861/500000000000000000000000) (301226284192030374100419/500000000000000000000000) (6522135023290589/1000000000000000000000000) where
  r0 := (70631592391/125000000000000000)
  k0 := (1776860202682727/500000000000000000)
  k6 := (353764013634271/31250000000000000)
  q := (85530696244097066277/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14631]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14631]

theorem width_14632 : mW 14632 = 378933432312297 := by
  have hu : mW 14632 ≤ 378933432312297 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14632 ≤ 378933432312296 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14632 : RowArithmetic 14632 (552676391529166123249/500000000000000000000000) (602442151387439100214689/1000000000000000000000000) (1630244035509449/250000000000000000000000) where
  r0 := (141248703429/250000000000000000)
  k0 := (444192281115267/125000000000000000)
  k6 := (2264012318192479/200000000000000000)
  q := (17106723824274477367/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14632]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14632]

theorem width_14633 : mW 14633 = 379024081595983 := by
  have hu : mW 14633 ≤ 379024081595983 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14633 ≤ 379024081595982 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14633 : RowArithmetic 14633 (552662832305868656401/500000000000000000000000) (150607933950264648714693/250000000000000000000000) (1629954387153997/250000000000000000000000) where
  r0 := (564936898201/1000000000000000000)
  k0 := (3553356114266111/1000000000000000000)
  k6 := (11319674785283549/1000000000000000000)
  q := (171073083797539582437/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14633]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14633]

theorem width_14634 : mW 14634 = 379114746368124 := by
  have hu : mW 14634 ≤ 379114746368124 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14634 ≤ 379114746368123 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14634 : RowArithmetic 14634 (552649276181854655729/500000000000000000000000) (602421321624614075463089/1000000000000000000000000) (6518659242933397/1000000000000000000000000) where
  r0 := (564878992579/1000000000000000000)
  k0 := (3553174001388147/1000000000000000000)
  k6 := (11319288019253359/1000000000000000000)
  q := (171078929152599035083/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14634]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14634]

theorem width_14635 : mW 14635 = 379205426630308 := by
  have hu : mW 14635 ≤ 379205426630308 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14635 ≤ 379205426630307 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14635 : RowArithmetic 14635 (221054289262478661831/200000000000000000000000) (602410908857800591574513/1000000000000000000000000) (6517501224898271/1000000000000000000000000) where
  r0 := (35301318553/62500000000000000)
  k0 := (3552991910285303/1000000000000000000)
  k6 := (2829725323216263/250000000000000000)
  q := (171084774307943604337/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14635]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14635]

theorem width_14636 : mW 14636 = 379296122384124 := by
  have hu : mW 14636 ≤ 379296122384124 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14636 ≤ 379296122384123 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14636 : RowArithmetic 14636 (552622173227967315501/500000000000000000000000) (602400497500313149514787/1000000000000000000000000) (6516343494418881/1000000000000000000000000) where
  r0 := (564763211007/1000000000000000000)
  k0 := (3552809840957781/1000000000000000000)
  k6 := (11318514606111857/1000000000000000000)
  q := (17109061926359375943/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14636]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14636]

theorem width_14637 : mW 14637 = 379386833631158 := by
  have hu : mW 14637 ≤ 379386833631158 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14637 ≤ 379386833631157 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14637 : RowArithmetic 14637 (1105217252792480667967/1000000000000000000000000) (301195043775923501447763/500000000000000000000000) (1303037210280717/200000000000000000000000) where
  r0 := (141176333763/250000000000000000)
  k0 := (888156948349087/250000000000000000)
  k6 := (5659063979493501/500000000000000000)
  q := (85548232009784983049/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14637]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14637]

theorem width_14638 : mW 14638 = 379477560372999 := by
  have hu : mW 14638 ≤ 379477560372999 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14638 ≤ 379477560372998 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14638 : RowArithmetic 14638 (221038033064035632913/200000000000000000000000) (602379679012097281138413/1000000000000000000000000) (260561155830429/40000000000000000000000) where
  r0 := (282323734491/500000000000000000)
  k0 := (3552445767601203/1000000000000000000)
  k6 := (5658870675741861/500000000000000000)
  q := (171102308575892686581/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14638]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14638]

theorem width_14639 : mW 14639 = 379568302611235 := by
  have hu : mW 14639 ≤ 379568302611235 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14639 ≤ 379568302611234 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14639 : RowArithmetic 14639 (55258154201858751333/50000000000000000000000) (602369271880759422950301/1000000000000000000000000) (3256436013699349/500000000000000000000000) where
  r0 := (282294806397/500000000000000000)
  k0 := (222016485222891/62500000000000000)
  k6 := (707334673974703/62500000000000000)
  q := (21388519116572797453/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14639]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14639]

theorem width_14640 : mW 14640 = 379659060347453 := by
  have hu : mW 14640 ≤ 379659060347453 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14640 ≤ 379659060347452 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14640 : RowArithmetic 14640 (1105136008941620320219/1000000000000000000000000) (602358866157528823686691/1000000000000000000000000) (3255857723112977/500000000000000000000000) where
  r0 := (282265883243/500000000000000000)
  k0 := (3552081781288559/1000000000000000000)
  k6 := (11316968255314817/1000000000000000000)
  q := (171113997089659500479/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14640]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14640]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 14626 then ⟨(138189453001469732049/125000000000000000000000), (602504674531471045990411/1000000000000000000000000), (1305586750046841/200000000000000000000000)⟩ else
  if n = 14627 then ⟨(1105488468334773355259/1000000000000000000000000), (602494250479063945522783/1000000000000000000000000), (6526773428448507/1000000000000000000000000)⟩ else
  if n = 14628 then ⟨(552730659433749479201/500000000000000000000000), (602483827838424884034457/1000000000000000000000000), (6525613394953243/1000000000000000000000000)⟩ else
  if n = 14629 then ⟨(1105434175608075464823/1000000000000000000000000), (60247340660924828741139/100000000000000000000000), (6524453649656443/1000000000000000000000000)⟩ else
  if n = 14630 then ⟨(552703519277322419469/500000000000000000000000), (60246298679122871884239/100000000000000000000000), (652329419246619/100000000000000000000000)⟩ else
  if n = 14631 then ⟨(552689953852674651861/500000000000000000000000), (301226284192030374100419/500000000000000000000000), (6522135023290589/1000000000000000000000000)⟩ else
  if n = 14632 then ⟨(552676391529166123249/500000000000000000000000), (602442151387439100214689/1000000000000000000000000), (1630244035509449/250000000000000000000000)⟩ else
  if n = 14633 then ⟨(552662832305868656401/500000000000000000000000), (150607933950264648714693/250000000000000000000000), (1629954387153997/250000000000000000000000)⟩ else
  if n = 14634 then ⟨(552649276181854655729/500000000000000000000000), (602421321624614075463089/1000000000000000000000000), (6518659242933397/1000000000000000000000000)⟩ else
  if n = 14635 then ⟨(221054289262478661831/200000000000000000000000), (602410908857800591574513/1000000000000000000000000), (6517501224898271/1000000000000000000000000)⟩ else
  if n = 14636 then ⟨(552622173227967315501/500000000000000000000000), (602400497500313149514787/1000000000000000000000000), (6516343494418881/1000000000000000000000000)⟩ else
  if n = 14637 then ⟨(1105217252792480667967/1000000000000000000000000), (301195043775923501447763/500000000000000000000000), (1303037210280717/200000000000000000000000)⟩ else
  if n = 14638 then ⟨(221038033064035632913/200000000000000000000000), (602379679012097281138413/1000000000000000000000000), (260561155830429/40000000000000000000000)⟩ else
  if n = 14639 then ⟨(55258154201858751333/50000000000000000000000), (602369271880759422950301/1000000000000000000000000), (3256436013699349/500000000000000000000000)⟩ else
  ⟨(1105136008941620320219/1000000000000000000000000), (602358866157528823686691/1000000000000000000000000), (3255857723112977/500000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14626 ≤ n) (hb : n ≤ 14640) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14626
  · exact row_14627
  · exact row_14628
  · exact row_14629
  · exact row_14630
  · exact row_14631
  · exact row_14632
  · exact row_14633
  · exact row_14634
  · exact row_14635
  · exact row_14636
  · exact row_14637
  · exact row_14638
  · exact row_14639
  · exact row_14640

end BstLean.Part271.R3.Rows14626
