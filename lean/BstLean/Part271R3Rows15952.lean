import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15952–16026. -/
namespace BstLean.Part271.R3.Rows15952
open Real BstLean.Part130 BstLean.Part227

theorem width_15952 : mW 15952 = 512687812234038 := by
  have hu : mW 15952 ≤ 512687812234038 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15952 ≤ 512687812234037 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15952 : RowArithmetic 15952 (1074320494248896824589/1000000000000000000000000) (589814702754751258659597/1000000000000000000000000) (2605520993762789/500000000000000000000000) where
  r0 := (2481688641/5000000000000000)
  k0 := (3330637810580731/1000000000000000000)
  k6 := (5420796075326097/500000000000000000)
  q := (178616908494128853009/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15952]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15952]

theorem width_15953 : mW 15953 = 512800308971572 := by
  have hu : mW 15953 ≤ 512800308971572 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15953 ≤ 512800308971571 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15953 : RowArithmetic 15953 (1074300171980160233949/1000000000000000000000000) (58980591355604395498619/100000000000000000000000) (5210195186713331/1000000000000000000000000) where
  r0 := (24814553009/50000000000000000)
  k0 := (3330481225742461/1000000000000000000)
  k6 := (10841252347415971/1000000000000000000)
  q := (8931125349025171979/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15953]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15953]

theorem width_15954 : mW 15954 = 512912823339888 := by
  have hu : mW 15954 ≤ 512912823339888 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15954 ≤ 512912823339887 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15954 : RowArithmetic 15954 (1074279853959917540009/1000000000000000000000000) (147449281358039806763901/250000000000000000000000) (5209348578289883/1000000000000000000000000) where
  r0 := (496244399473/1000000000000000000)
  k0 := (3330324658080883/1000000000000000000)
  k6 := (10840912576128653/1000000000000000000)
  q := (22328513161426579861/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15954]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15954]

theorem width_15955 : mW 15955 = 513025355340645 := by
  have hu : mW 15955 ≤ 513025355340645 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15955 ≤ 513025355340644 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15955 : RowArithmetic 15955 (107425954018700528333/100000000000000000000000) (589788338382887034460757/1000000000000000000000000) (1041700432439819/200000000000000000000000) where
  r0 := (496197746077/1000000000000000000)
  k0 := (333016810759171/100000000000000000)
  k6 := (2710143209196309/250000000000000000)
  q := (11164606464179559249/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15955]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15955]

theorem width_15956 : mW 15956 = 513137904975501 := by
  have hu : mW 15956 ≤ 513137904975501 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15956 ≤ 513137904975500 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15956 : RowArithmetic 15956 (1074239230660260685993/1000000000000000000000000) (589779552408017247222959/1000000000000000000000000) (5207655938384859/1000000000000000000000000) where
  r0 := (49615109999/100000000000000000)
  k0 := (832502893567663/250000000000000000)
  k6 := (1355029141172589/125000000000000000)
  q := (35727860277380172267/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15956]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15956]

theorem width_15957 : mW 15957 = 513250472246113 := by
  have hu : mW 15957 ≤ 513250472246113 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15957 ≤ 513250472246112 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15957 : RowArithmetic 15957 (1074218925378521650913/1000000000000000000000000) (23590830700293594761371/40000000000000000000000) (2603404953395547/500000000000000000000000) where
  r0 := (124026115303/250000000000000000)
  k0 := (52028985283127/15625000000000000)
  k6 := (10839893453910079/1000000000000000000)
  q := (178644899171512870823/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15957]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15957]

theorem width_15958 : mW 15958 = 513363057154140 := by
  have hu : mW 15958 ≤ 513363057154140 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15958 ≤ 513363057154139 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15958 : RowArithmetic 15958 (537099312170312970727/500000000000000000000000) (29488099184032247022349/50000000000000000000000) (1301491016840431/250000000000000000000000) where
  r0 := (496057829739/1000000000000000000)
  k0 := (3329698559129137/1000000000000000000)
  k6 := (5419776905184167/500000000000000000)
  q := (89325248390362732873/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15958]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15958]

theorem width_15959 : mW 15959 = 513475659701239 := by
  have hu : mW 15959 ≤ 513475659701239 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15959 ≤ 513475659701238 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15959 : RowArithmetic 15959 (537089163772706137391/500000000000000000000000) (589753200927722618232379/1000000000000000000000000) (5205118420040709/1000000000000000000000000) where
  r0 := (124002801393/250000000000000000)
  k0 := (665908415460691/200000000000000000)
  k6 := (433568567950019/40000000000000000)
  q := (178656094214555132819/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15959]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15959]

theorem width_15960 : mW 15960 = 513588279889068 := by
  have hu : mW 15960 ≤ 513588279889068 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15960 ≤ 513588279889067 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15960 : RowArithmetic 15960 (134269754373964937697/125000000000000000000000) (589744419248363009110281/1000000000000000000000000) (650534120596503/125000000000000000000000) where
  r0 := (123991147177/250000000000000000)
  k0 := (3329385612635431/1000000000000000000)
  k6 := (21677749238103/2000000000000000)
  q := (7146467658920734247/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15960]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15960]

theorem width_15961 : mW 15961 = 513700917719287 := by
  have hu : mW 15961 ≤ 513700917719287 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15961 ≤ 513700917719286 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15961 : RowArithmetic 15961 (33566804583699572919/31250000000000000000000) (147433909660589099813581/250000000000000000000000) (130085692537491/25000000000000000000000) where
  r0 := (99183595829/200000000000000000)
  k0 := (832307291280193/250000000000000000)
  k6 := (2709633767816603/250000000000000000)
  q := (44666822139032904341/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15961]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15961]

theorem width_15962 : mW 15962 = 513813573193552 := by
  have hu : mW 15962 ≤ 513813573193552 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15962 ≤ 513813573193551 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15962 : RowArithmetic 15962 (1074117462604252980571/1000000000000000000000000) (589726859109493043912871/1000000000000000000000000) (5202582630167591/1000000000000000000000000) where
  r0 := (247935688441/500000000000000000)
  k0 := (166453636737927/50000000000000000)
  k6 := (1083819555539021/100000000000000000)
  q := (35734577092782279071/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15962]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15962]

theorem width_15963 : mW 15963 = 513926246313522 := by
  have hu : mW 15963 ≤ 513926246313522 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15963 ≤ 513926246313521 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15963 : RowArithmetic 15963 (1074097182768159240743/1000000000000000000000000) (294859040324781637324991/500000000000000000000000) (2600868875359951/500000000000000000000000) where
  r0 := (247912390959/500000000000000000)
  k0 := (665783264309559/200000000000000000)
  k6 := (5418928035708949/500000000000000000)
  q := (178678482196374166537/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15963]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15963]

theorem width_15964 : mW 15964 = 514038937080855 := by
  have hu : mW 15964 ≤ 514038937080855 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15964 ≤ 514038937080854 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15964 : RowArithmetic 15964 (1074076907168945590853/1000000000000000000000000) (58970930326235743790581/100000000000000000000000) (1300223265775157/250000000000000000000000) where
  r0 := (1983112777/4000000000000000)
  k0 := (832189981370221/250000000000000000)
  k6 := (10837516619344479/1000000000000000000)
  q := (44671019688384101179/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15964]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15964]

theorem width_15965 : mW 15965 = 514151645497209 := by
  have hu : mW 15965 ≤ 514151645497209 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15965 ≤ 514151645497208 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15965 : RowArithmetic 15965 (537028317902726456927/500000000000000000000000) (589700526947666094743561/1000000000000000000000000) (2600024283626921/500000000000000000000000) where
  r0 := (247865806939/500000000000000000)
  k0 := (104018860830007/31250000000000000)
  k6 := (10837177199164959/1000000000000000000)
  q := (89344837567707290561/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15965]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15965]

theorem width_15966 : mW 15966 = 514264371564244 := by
  have hu : mW 15966 ≤ 514264371564244 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15966 ≤ 514264371564243 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15966 : RowArithmetic 15966 (537018184338260976833/500000000000000000000000) (589691751705279617757741/1000000000000000000000000) (259960213156181/50000000000000000000000) where
  r0 := (495685040799/1000000000000000000)
  k0 := (3328447184778159/1000000000000000000)
  k6 := (5418418905437171/500000000000000000)
  q := (89347635671012582201/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15966]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15966]

theorem width_15967 : mW 15967 = 514377115283616 := by
  have hu : mW 15967 ≤ 514377115283616 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15967 ≤ 514377115283615 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15967 : RowArithmetic 15967 (1074016105780994950019/1000000000000000000000000) (9213796523984198076109/15625000000000000000000) (5198360150654099/1000000000000000000000000) where
  r0 := (123909618753/250000000000000000)
  k0 := (3328290840133747/1000000000000000000)
  k6 := (10836498454467637/1000000000000000000)
  q := (89350433686692310313/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15967]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15967]

theorem width_15968 : mW 15968 = 514489876656986 := by
  have hu : mW 15968 ≤ 514489876656986 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15968 ≤ 514489876656985 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15968 : RowArithmetic 15968 (268498961779428296531/250000000000000000000000) (58967420443658381803487/100000000000000000000000) (5197516229789383/1000000000000000000000000) where
  r0 := (99118383303/200000000000000000)
  k0 := (3328134512622687/1000000000000000000)
  k6 := (216723182598797/20000000000000000)
  q := (178706463229509413287/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15968]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15968]

theorem width_15969 : mW 15969 = 514602655686010 := by
  have hu : mW 15969 ≤ 514602655686010 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15969 ≤ 514602655686009 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15969 : RowArithmetic 15969 (536987796342759856191/500000000000000000000000) (58966543240985575373113/100000000000000000000000) (5196672500473651/1000000000000000000000000) where
  r0 := (123886341327/250000000000000000)
  k0 := (665595640449479/200000000000000000)
  k6 := (1354477479660749/125000000000000000)
  q := (178712058910416003299/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15969]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15969]

theorem width_15970 : mW 15970 = 514715452372349 := by
  have hu : mW 15970 ≤ 514715452372349 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15970 ≤ 514715452372348 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15970 : RowArithmetic 15970 (1073955342483256623293/1000000000000000000000000) (589656661454595200436863/1000000000000000000000000) (649478620331381/125000000000000000000000) where
  r0 := (495498821387/1000000000000000000)
  k0 := (831955477249213/250000000000000000)
  k6 := (677217536031317/62500000000000000)
  q := (178717654416120848999/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15970]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15970]

theorem width_15971 : mW 15971 = 514828266717659 := by
  have hu : mW 15971 ≤ 514828266717659 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15971 ≤ 514828266717658 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15971 : RowArithmetic 15971 (214787019301953555839/200000000000000000000000) (589647891570592937854997/1000000000000000000000000) (81171650254153/15625000000000000000000) where
  r0 := (30965767797/62500000000000000)
  k0 := (3249673469603/976562500000000)
  k6 := (5417570673790051/500000000000000000)
  q := (178723249746640406147/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15971]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15971]

theorem width_15972 : mW 15972 = 514941098723601 := by
  have hu : mW 15972 ≤ 514941098723601 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15972 ≤ 514941098723600 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15972 : RowArithmetic 15972 (1073914854763896085147/1000000000000000000000000) (294819561378819895682619/500000000000000000000000) (5194142461262071/1000000000000000000000000) where
  r0 := (495405755401/1000000000000000000)
  k0 := (66550187477459/20000000000000000)
  k6 := (2166960430103619/200000000000000000)
  q := (178728844901991127931/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15972]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15972]

theorem width_15973 : mW 15973 = 515053948391833 := by
  have hu : mW 15973 ≤ 515053948391833 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15973 ≤ 515053948391832 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15973 : RowArithmetic 15973 (1073894617244485667193/1000000000000000000000000) (294815177507763355549093/500000000000000000000000) (5193299497584123/1000000000000000000000000) where
  r0 := (495359233333/1000000000000000000)
  k0 := (3327353131994341/1000000000000000000)
  k6 := (10834462985310063/1000000000000000000)
  q := (89367219941094732479/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15973]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15973]

theorem width_15974 : mW 15974 = 515166815724013 := by
  have hu : mW 15974 ≤ 515166815724013 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15974 ≤ 515166815724012 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15974 : RowArithmetic 15974 (214774876790076211151/200000000000000000000000) (589621588344044613262581/1000000000000000000000000) (5192456725176207/1000000000000000000000000) where
  r0 := (99062543709/200000000000000000)
  k0 := (3327196907229981/1000000000000000000)
  k6 := (5417061925975511/500000000000000000)
  q := (11171252167953241579/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15974]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15974]

theorem width_15975 : mW 15975 = 515279700721800 := by
  have hu : mW 15975 ≤ 515279700721800 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15975 ≤ 515279700721799 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15975 : RowArithmetic 15975 (134231769360053364237/125000000000000000000000) (589612822742984463957803/1000000000000000000000000) (519161414398259/100000000000000000000000) where
  r0 := (123816552759/250000000000000000)
  k0 := (1663520349789461/500000000000000000)
  k6 := (2708446187608997/250000000000000000)
  q := (178745629317194774311/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15975]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15975]

theorem width_15976 : mW 15976 = 515392603386854 := by
  have hu : mW 15976 ≤ 515392603386854 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15976 ≤ 515392603386853 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15976 : RowArithmetic 15976 (268458482508367009409/250000000000000000000000) (589604058212137417535697/1000000000000000000000000) (5190771753947553/1000000000000000000000000) where
  r0 := (99043942161/200000000000000000)
  k0 := (665376901808043/200000000000000000)
  k6 := (1354180710094997/125000000000000000)
  q := (89375611886017317493/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15976]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15976]

theorem width_15977 : mW 15977 = 515505523720833 := by
  have hu : mW 15977 ≤ 515505523720833 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15977 ≤ 515505523720832 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15977 : RowArithmetic 15977 (1073813709408350170313/1000000000000000000000000) (147398823687823644146549/250000000000000000000000) (1037985911003083/200000000000000000000000) where
  r0 := (9903464357/20000000000000000)
  k0 := (207920520975597/62500000000000000)
  k6 := (2166621328583601/200000000000000000)
  q := (89378409025893943801/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15977]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15977]

theorem width_15978 : mW 15978 = 515618461725396 := by
  have hu : mW 15978 ≤ 515618461725396 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15978 ≤ 515618461725395 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15978 : RowArithmetic 15978 (536896746501959593829/500000000000000000000000) (73698316545030883389179/125000000000000000000000) (1037817509426101/200000000000000000000000) where
  r0 := (495126732169/1000000000000000000)
  k0 := (26612577434261/8000000000000000)
  k6 := (5416383818452547/500000000000000000)
  q := (178762412156470969903/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15978]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15978]

theorem width_15979 : mW 15979 = 515731417402202 := by
  have hu : mW 15979 ≤ 515731417402202 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15979 ≤ 515731417402201 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15979 : RowArithmetic 15979 (134221660102377671157/125000000000000000000000) (589577771038786166618677/1000000000000000000000000) (207529829209487/40000000000000000000000) where
  r0 := (495080253761/1000000000000000000)
  k0 := (1663208020029241/500000000000000000)
  k6 := (1354053582839533/125000000000000000)
  q := (89384003043050158529/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15979]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15979]

theorem width_15980 : mW 15980 = 515844390752910 := by
  have hu : mW 15980 ≤ 515844390752910 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15980 ≤ 515844390752909 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15980 : RowArithmetic 15980 (33554783526640731199/31250000000000000000000) (11791380215734063045917/20000000000000000000000) (5187404104279793/1000000000000000000000000) where
  r0 := (3960270261/8000000000000000)
  k0 := (3326259917936173/1000000000000000000)
  k6 := (5416044860173267/500000000000000000)
  q := (35754719968138472333/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15980]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15980]

theorem width_15981 : mW 15981 = 515957381779180 := by
  have hu : mW 15981 ≤ 515957381779180 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15981 ≤ 515957381779179 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15981 : RowArithmetic 15981 (536866434551606045393/500000000000000000000000) (36847515725236834084817/62500000000000000000000) (5186562669202741/1000000000000000000000000) where
  r0 := (247493659379/500000000000000000)
  k0 := (133044152516321/40000000000000000)
  k6 := (676984425611933/62500000000000000)
  q := (178779193420263533753/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15981]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15981]

theorem width_15982 : mW 15982 = 516070390482670 := by
  have hu : mW 15982 ≤ 516070390482670 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15982 ≤ 516070390482669 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15982 : RowArithmetic 15982 (1073712669569995207723/1000000000000000000000000) (589551493489836213921711/1000000000000000000000000) (129643035623761/25000000000000000000000) where
  r0 := (494940862159/1000000000000000000)
  k0 := (3325947724973087/1000000000000000000)
  k6 := (10831411931044469/1000000000000000000)
  q := (8939239341241513039/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15982]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15982]

theorem width_15983 : mW 15983 = 516183416865040 := by
  have hu : mW 15983 ≤ 516183416865040 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15983 ≤ 516183416865039 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15983 : RowArithmetic 15983 (214738494850340074321/200000000000000000000000) (589542736444635150934337/1000000000000000000000000) (5184880371467311/1000000000000000000000000) where
  r0 := (494894412827/1000000000000000000)
  k0 := (665158330826081/200000000000000000)
  k6 := (5415536542051091/500000000000000000)
  q := (89395190027204483817/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15983]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15983]

theorem width_15984 : mW 15984 = 516296460927949 := by
  have hu : mW 15984 ≤ 516296460927949 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15984 ≤ 516296460927948 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15984 : RowArithmetic 15984 (1073672283147175878853/1000000000000000000000000) (23581359218719107380963/40000000000000000000000) (2592019754348903/500000000000000000000000) where
  r0 := (494847970759/1000000000000000000)
  k0 := (207852225023269/62500000000000000)
  k6 := (10830734268959091/1000000000000000000)
  q := (22349496638627009579/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15984]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15984]

theorem width_15985 : mW 15985 = 516409522673056 := by
  have hu : mW 15985 ≤ 516409522673056 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15985 ≤ 516409522673055 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15985 : RowArithmetic 15985 (1073652096255270428653/1000000000000000000000000) (589525225559655418972923/1000000000000000000000000) (5183198836586397/1000000000000000000000000) where
  r0 := (98960307191/200000000000000000)
  k0 := (3325479563701189/1000000000000000000)
  k6 := (676899717850639/62500000000000000)
  q := (22350195748583500941/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15985]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15985]

theorem width_15986 : mW 15986 = 516522602102022 := by
  have hu : mW 15986 ≤ 516522602102022 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15986 ≤ 516522602102021 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15986 : RowArithmetic 15986 (13420398919685407273/12500000000000000000000) (147379117929864988910797/250000000000000000000000) (1036471671015511/200000000000000000000000) where
  r0 := (123688777103/250000000000000000)
  k0 := (665064708821877/200000000000000000)
  k6 := (676878545878163/62500000000000000)
  q := (178807158693381177501/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15986]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15986]

theorem width_15987 : mW 15987 = 516635699216504 := by
  have hu : mW 15987 ≤ 516635699216504 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15987 ≤ 516635699216503 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15987 : RowArithmetic 15987 (214722347020942476779/200000000000000000000000) (294753859473591469794413/500000000000000000000000) (2590759032057907/500000000000000000000000) where
  r0 := (494708688129/1000000000000000000)
  k0 := (665033508319187/200000000000000000)
  k6 := (1353714751784409/125000000000000000)
  q := (178812751223172001169/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15987]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15987]

theorem width_15988 : mW 15988 = 516748814018164 := by
  have hu : mW 15988 ≤ 516748814018164 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15988 ≤ 516748814018163 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15988 : RowArithmetic 15988 (134198945105469866299/125000000000000000000000) (589498967242616162899759/1000000000000000000000000) (207227118545827/40000000000000000000000) where
  r0 := (98932455021/200000000000000000)
  k0 := (3325011556159881/1000000000000000000)
  k6 := (5414689663139623/500000000000000000)
  q := (178818343578056890579/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15988]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15988]

theorem width_15989 : mW 15989 = 516861946508659 := by
  have hu : mW 15989 ≤ 516861946508659 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15989 ≤ 516861946508658 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15989 : RowArithmetic 15989 (1073571390790823070961/1000000000000000000000000) (73686277075693927733153/125000000000000000000000) (80934969587683/15625000000000000000000) where
  r0 := (247307934669/500000000000000000)
  k0 := (664971117559381/200000000000000000)
  k6 := (5414520335028781/500000000000000000)
  q := (178823935758052255213/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15989]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15989]

theorem width_15990 : mW 15990 = 516975096689651 := by
  have hu : mW 15990 ≤ 516975096689651 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15990 ≤ 516975096689650 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15990 : RowArithmetic 15990 (134193903118094338243/125000000000000000000000) (589481467035780513882191/1000000000000000000000000) (5178998333958467/1000000000000000000000000) where
  r0 := (247284735413/500000000000000000)
  k0 := (103896863640709/31250000000000000)
  k6 := (43314808182421/4000000000000000)
  q := (178829527763174501987/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15990]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15990]

theorem width_15991 : mW 15991 = 517088264562798 := by
  have hu : mW 15991 ≤ 517088264562798 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15991 ≤ 517088264562797 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15991 : RowArithmetic 15991 (536765531652202609211/500000000000000000000000) (73684089816636917578617/125000000000000000000000) (323634925289409/62500000000000000000000) where
  r0 := (30907692473/62500000000000000)
  k0 := (3324543702276269/1000000000000000000)
  k6 := (338386357903667/31250000000000000)
  q := (89417559796720017627/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15991]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15991]

theorem width_15992 : mW 15992 = 517201450129760 := by
  have hu : mW 15992 ≤ 517201450129760 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15992 ≤ 517201450129759 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15992 : RowArithmetic 15992 (53675545293431292641/50000000000000000000000) (294731985548643977594773/500000000000000000000000) (2588659732786273/500000000000000000000000) where
  r0 := (247238347781/500000000000000000)
  k0 := (3324387785113329/1000000000000000000)
  k6 := (10828024891988879/1000000000000000000)
  q := (178840711248865256799/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15992]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15992]

theorem width_15993 : mW 15993 = 517314653392197 := by
  have hu : mW 15993 ≤ 517314653392197 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15993 ≤ 517314653392196 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15993 : RowArithmetic 15993 (214698150527253651053/200000000000000000000000) (589455224728150280735541/1000000000000000000000000) (2588240158364549/500000000000000000000000) where
  r0 := (494430318807/1000000000000000000)
  k0 := (664846377002581/200000000000000000)
  k6 := (1082768636281489/100000000000000000)
  q := (35769260545893313169/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15993]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15993]

theorem width_15994 : mW 15994 = 517427874351769 := by
  have hu : mW 15994 ≤ 517427874351769 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15994 ≤ 517427874351768 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15994 : RowArithmetic 15994 (536735301803092236699/500000000000000000000000) (589446479425474437419003/1000000000000000000000000) (2587820679022421/500000000000000000000000) where
  r0 := (494383949301/1000000000000000000)
  k0 := (831019000492669/250000000000000000)
  k6 := (10827347865390413/1000000000000000000)
  q := (178851894035260359051/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15994]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15994]

theorem width_15995 : mW 15995 = 517541113010136 := by
  have hu : mW 15995 ≤ 517541113010136 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15995 ≤ 517541113010135 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15995 : RowArithmetic 15995 (1073450458777226956199/1000000000000000000000000) (589437735189052523043861/1000000000000000000000000) (5174802589464443/1000000000000000000000000) where
  r0 := (247168793521/500000000000000000)
  k0 := (3323920135982317/1000000000000000000)
  k6 := (2165401879942097/200000000000000000)
  q := (89428742583131515257/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15995]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15995]

theorem width_15996 : mW 15996 = 517654369368957 := by
  have hu : mW 15996 ≤ 517654369368957 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15996 ≤ 517654369368956 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15996 : RowArithmetic 15996 (1073430318148248823281/1000000000000000000000000) (58942899201867671743539/100000000000000000000000) (1293491002733149/250000000000000000000000) where
  r0 := (123572808007/250000000000000000)
  k0 := (3323764287043503/1000000000000000000)
  k6 := (5413335482885073/500000000000000000)
  q := (22357884515311371471/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15996]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15996]

theorem width_15997 : mW 15997 = 517767643429893 := by
  have hu : mW 15997 ≤ 517767643429893 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15997 ≤ 517767643429892 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15997 : RowArithmetic 15997 (134176272714762882009/125000000000000000000000) (117884049982827858315077/200000000000000000000000) (2586562811196997/500000000000000000000000) where
  r0 := (494244884259/1000000000000000000)
  k0 := (415451056894579/125000000000000000)
  k6 := (2165266512712887/200000000000000000)
  q := (22358583362995071473/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15997]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15997]

theorem width_15998 : mW 15998 = 517880935194603 := by
  have hu : mW 15998 ≤ 517880935194603 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15998 ≤ 517880935194602 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15998 : RowArithmetic 15998 (268347512371410893939/250000000000000000000000) (147352877218808134115621/250000000000000000000000) (1293071855948343/250000000000000000000000) where
  r0 := (494198543733/1000000000000000000)
  k0 := (1661726320158689/500000000000000000)
  k6 := (10825994193088393/1000000000000000000)
  q := (178874257510688216973/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15998]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15998]

theorem width_15999 : mW 15999 = 517994244664748 := by
  have hu : mW 15999 ≤ 517994244664748 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15999 ≤ 517994244664747 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15999 : RowArithmetic 15999 (1073369921449724165357/1000000000000000000000000) (147350692225437185751221/250000000000000000000000) (1034289883015093/200000000000000000000000) where
  r0 := (30884513153/62500000000000000)
  k0 := (664659368504283/200000000000000000)
  k6 := (5412827927168531/500000000000000000)
  q := (89439923971345145593/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15999]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15999]

theorem width_16000 : mW 16000 = 518107571841988 := by
  have hu : mW 16000 ≤ 518107571841988 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16000 ≤ 518107571841987 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16000 : RowArithmetic 16000 (1073349797609199277813/1000000000000000000000000) (589394029993480415101617/1000000000000000000000000) (2585305798092519/500000000000000000000000) where
  r0 := (247052942201/500000000000000000)
  k0 := (830785265441103/250000000000000000)
  k6 := (2706329386826371/250000000000000000)
  q := (178885438199983175713/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16000]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16000]

theorem width_16001 : mW 16001 = 518220916727982 := by
  have hu : mW 16001 ≤ 518220916727982 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16001 ≤ 518220916727981 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16001 : RowArithmetic 16001 (1073329677962924035303/1000000000000000000000000) (589385292150219909147681/1000000000000000000000000) (1033954793413377/200000000000000000000000) where
  r0 := (247029782797/500000000000000000)
  k0 := (830746324511351/250000000000000000)
  k6 := (10824979271988703/1000000000000000000)
  q := (35778205656516649857/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16001]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16001]

theorem width_16002 : mW 16002 = 518334279324392 := by
  have hu : mW 16002 ≤ 518334279324392 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16002 ≤ 518334279324391 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16002 : RowArithmetic 16002 (268327390627438288249/250000000000000000000000) (589376555371759838733273/1000000000000000000000000) (40382316622389/7812500000000000000000) where
  r0 := (247006627011/500000000000000000)
  k0 := (3322829551360061/1000000000000000000)
  k6 := (2164928205676353/200000000000000000)
  q := (178896618190506888073/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16002]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16002]

theorem width_16003 : mW 16003 = 518447659632877 := by
  have hu : mW 16003 ≤ 518447659632877 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16003 ≤ 518447659632876 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16003 : RowArithmetic 16003 (1073289451248542553123/1000000000000000000000000) (294683909828946343822409/500000000000000000000000) (1033619855585319/200000000000000000000000) where
  r0 := (98793389937/200000000000000000)
  k0 := (1661336910853707/500000000000000000)
  k6 := (10824302816479717/1000000000000000000)
  q := (17890220792377046569/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16003]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16003]

theorem width_16004 : mW 16004 = 518561057655098 := by
  have hu : mW 16004 ≤ 518561057655098 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16004 ≤ 518561057655097 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16004 : RowArithmetic 16004 (1073269344178148019831/1000000000000000000000000) (117871817001682235530191/200000000000000000000000) (5167262217794127/1000000000000000000000000) where
  r0 := (493920652581/1000000000000000000)
  k0 := (830629527270783/250000000000000000)
  k6 := (2705991159069401/250000000000000000)
  q := (178907797482390353193/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16004]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16004]

theorem width_16005 : mW 16005 = 518674473392715 := by
  have hu : mW 16005 ≤ 518674473392715 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16005 ≤ 518674473392714 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16005 : RowArithmetic 16005 (536624620648713002893/500000000000000000000000) (294675175711553950381249/500000000000000000000000) (645803168401657/125000000000000000000000) where
  r0 := (493874362709/1000000000000000000)
  k0 := (1661181206743123/500000000000000000)
  k6 := (2705906621942619/250000000000000000)
  q := (89456693433191459539/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16005]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16005]

theorem width_16006 : mW 16006 = 518787906847388 := by
  have hu : mW 16006 ≤ 518787906847388 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16006 ≤ 518787906847387 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16006 : RowArithmetic 16006 (536614571302616681499/500000000000000000000000) (4714732951214205295499/8000000000000000000000) (2582794333064433/500000000000000000000000) where
  r0 := (493828080067/1000000000000000000)
  k0 := (1661103367456211/500000000000000000)
  k6 := (5411644185476691/500000000000000000)
  q := (178918976075764529287/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16006]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16006]

theorem width_16007 : mW 16007 = 518901358020779 := by
  have hu : mW 16007 ≤ 518901358020779 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16007 ≤ 518901358020778 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16007 : RowArithmetic 16007 (268302262025106701457/250000000000000000000000) (58933288744420722902027/100000000000000000000000) (5164752174485843/1000000000000000000000000) where
  r0 := (493781804653/1000000000000000000)
  k0 := (132882042934293/40000000000000000)
  k6 := (2705737571455343/250000000000000000)
  q := (89462282555275773603/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16007]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16007]

theorem width_16008 : mW 16008 = 519014826914547 := by
  have hu : mW 16008 ≤ 519014826914547 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16008 ≤ 519014826914546 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16008 : RowArithmetic 16008 (1073188957781864253331/1000000000000000000000000) (2946620785250977127029/5000000000000000000000) (2581957936114561/500000000000000000000000) where
  r0 := (246867768233/500000000000000000)
  k0 := (207618464301249/62500000000000000)
  k6 := (5411306116184749/500000000000000000)
  q := (5591567311586260427/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16008]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16008]

theorem width_16009 : mW 16009 = 519128313530353 := by
  have hu : mW 16009 ≤ 519128313530353 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16009 ≤ 519128313530352 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16009 : RowArithmetic 16009 (134146108956050435819/125000000000000000000000) (117863085543906642479809/200000000000000000000000) (5163079759303641/1000000000000000000000000) where
  r0 := (30855579719/62500000000000000)
  k0 := (1660869900648031/500000000000000000)
  k6 := (10822274210592813/1000000000000000000)
  q := (22366967832050905867/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16009]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16009]

theorem width_16010 : mW 16010 = 519241817869858 := by
  have hu : mW 16010 ≤ 519241817869858 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16010 ≤ 519241817869857 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16010 : RowArithmetic 16010 (21462975793978053711/20000000000000000000000) (589306699452013522975973/1000000000000000000000000) (5162243835654353/1000000000000000000000000) where
  r0 := (98728604353/200000000000000000)
  k0 := (3321584190781223/1000000000000000000)
  k6 := (10821936220486371/1000000000000000000)
  q := (178941331167508642741/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16010]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16010]

theorem width_16011 : mW 16011 = 519355339934722 := by
  have hu : mW 16011 ≤ 519355339934722 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16011 ≤ 519355339934721 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16011 : RowArithmetic 16011 (536564355966110348617/500000000000000000000000) (147324493061857339722051/250000000000000000000000) (2580704050613123/500000000000000000000000) where
  r0 := (493596775249/1000000000000000000)
  k0 := (3321428597277857/1000000000000000000)
  k6 := (5410799131022613/500000000000000000)
  q := (35789383900816174849/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16011]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16011]

theorem width_16012 : mW 16012 = 519468879726607 := by
  have hu : mW 16012 ≤ 519468879726607 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16012 ≤ 519468879726606 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16012 : RowArithmetic 16012 (1073108638347216230939/1000000000000000000000000) (294644623052786903412757/500000000000000000000000) (1032114511192861/200000000000000000000000) where
  r0 := (246775267977/500000000000000000)
  k0 := (26570184166253/8000000000000000)
  k6 := (5410630167632217/500000000000000000)
  q := (89476253833070146031/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16012]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16012]

theorem width_16013 : mW 16013 = 519582437247172 := by
  have hu : mW 16013 ≤ 519582437247172 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16013 ≤ 519582437247171 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16013 : RowArithmetic 16013 (107308856894274919833/100000000000000000000000) (589280521026240019328661/1000000000000000000000000) (2579868599906783/500000000000000000000000) where
  r0 := (493504303877/1000000000000000000)
  k0 := (415139682660603/125000000000000000)
  k6 := (10820922440139053/1000000000000000000)
  q := (178958095653703244251/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16013]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16013]

theorem width_16014 : mW 16014 = 519696012498080 := by
  have hu : mW 16014 ≤ 519696012498080 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16014 ≤ 519696012498079 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16014 : RowArithmetic 16014 (268267125929419709421/250000000000000000000000) (117854359401844219991813/200000000000000000000000) (1031780406543809/200000000000000000000000) where
  r0 := (493458079017/1000000000000000000)
  k0 := (830240479696619/250000000000000000)
  k6 := (541029228833207/50000000000000000)
  q := (178963683466786076319/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16014]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16014]

theorem width_16015 : mW 16015 = 519809605480990 := by
  have hu : mW 16015 ≤ 519809605480990 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16015 ≤ 519809605480989 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16015 : RowArithmetic 16015 (67065527666929116043/62500000000000000000000) (2301808883024649984607/3906250000000000000000) (2579033527312909/500000000000000000000000) where
  r0 := (246705930687/500000000000000000)
  k0 := (3320806393288971/1000000000000000000)
  k6 := (5410123372417377/500000000000000000)
  q := (89484635552702565611/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16015]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16015]

theorem width_16016 : mW 16016 = 519923216197564 := by
  have hu : mW 16016 ≤ 519923216197564 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16016 ≤ 519923216197563 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16016 : RowArithmetic 16016 (214605677160234111517/200000000000000000000000) (117850870432260215318141/200000000000000000000000) (5157232265478951/1000000000000000000000000) where
  r0 := (963604787/1953125000000000)
  k0 := (830162721195309/250000000000000000)
  k6 := (10819908944645957/1000000000000000000)
  q := (89487429284788374683/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16016]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16016]

theorem width_16017 : mW 16017 = 520036844649462 := by
  have hu : mW 16017 ≤ 520036844649462 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16017 ≤ 520036844649461 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16017 : RowArithmetic 16017 (1073008333107454175637/1000000000000000000000000) (589245631329986638204351/1000000000000000000000000) (103127953304471/20000000000000000000000) where
  r0 := (493319447727/1000000000000000000)
  k0 := (3320495393265657/1000000000000000000)
  k6 := (1352446397011601/125000000000000000)
  q := (44745111464829317151/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16017]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16017]

theorem width_16018 : mW 16018 = 520150490838346 := by
  have hu : mW 16018 ≤ 520150490838346 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16018 ≤ 520150490838345 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16018 : RowArithmetic 16018 (268247071147144452153/250000000000000000000000) (589236911560160340133831/1000000000000000000000000) (2577781626902361/500000000000000000000000) where
  r0 := (493273251721/1000000000000000000)
  k0 := (830084979684473/250000000000000000)
  k6 := (10819233439170371/1000000000000000000)
  q := (2237325412183037803/12500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16018]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16018]

theorem width_16019 : mW 16019 = 520264154765877 := by
  have hu : mW 16019 ≤ 520264154765877 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16019 ≤ 520264154765876 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16019 : RowArithmetic 16019 (214593648048680643861/200000000000000000000000) (147307048212903928743599/250000000000000000000000) (2577364515583801/500000000000000000000000) where
  r0 := (19729082517/40000000000000000)
  k0 := (3320184461196961/1000000000000000000)
  k6 := (10818895733873709/1000000000000000000)
  q := (44747904978892587257/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16019]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16019]

theorem width_16020 : mW 16020 = 520377836433716 := by
  have hu : mW 16020 ≤ 520377836433716 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16020 ≤ 520377836433715 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16020 : RowArithmetic 16020 (536474100035396283863/500000000000000000000000) (589219475204146263881179/1000000000000000000000000) (2576947498628673/500000000000000000000000) where
  r0 := (61647610167/125000000000000000)
  k0 := (207501813789697/62500000000000000)
  k6 := (10818558060197887/1000000000000000000)
  q := (7159888267284622927/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16020]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16020]

theorem width_16021 : mW 16021 = 520491535843524 := by
  have hu : mW 16021 ≤ 520491535843524 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16021 ≤ 520491535843523 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16021 : RowArithmetic 16021 (268232041017402102731/250000000000000000000000) (147302689654386384397929/250000000000000000000000) (515306115201913/100000000000000000000000) where
  r0 := (246567353477/500000000000000000)
  k0 := (3319873597054849/1000000000000000000)
  k6 := (1081822041813797/100000000000000000)
  q := (89501396637147512169/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16021]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16021]

theorem width_16022 : mW 16022 = 520605252996963 := by
  have hu : mW 16022 ≤ 520605252996963 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16022 ≤ 520605252996962 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16022 : RowArithmetic 16022 (536454066119356717927/500000000000000000000000) (294601021545803613875741/500000000000000000000000) (257611374769907/50000000000000000000000) where
  r0 := (493088539777/1000000000000000000)
  k0 := (3319718190451707/1000000000000000000)
  k6 := (432715312307561/40000000000000000)
  q := (89504189846062513813/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16022]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16022]

theorem width_16023 : mW 16023 = 520718987895693 := by
  have hu : mW 16023 ≤ 520718987895693 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16023 ≤ 520718987895692 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16023 : RowArithmetic 16023 (1072888104576971260243/1000000000000000000000000) (147298332156531228758299/250000000000000000000000) (2575697013669801/500000000000000000000000) where
  r0 := (246521189901/500000000000000000)
  k0 := (3319562800818009/1000000000000000000)
  k6 := (270438630721153/25000000000000000)
  q := (111883728709763691/625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16023]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16023]

theorem width_16024 : mW 16024 = 520832740541377 := by
  have hu : mW 16024 ≤ 520832740541377 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16024 ≤ 520832740541376 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16024 : RowArithmetic 16024 (1072868081083245097663/1000000000000000000000000) (36824038451305774472609/62500000000000000000000) (1287640186947183/250000000000000000000000) where
  r0 := (492996227029/1000000000000000000)
  k0 := (3319407428156139/1000000000000000000)
  k6 := (10817207681604323/1000000000000000000)
  q := (89509776002400989139/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16024]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16024]

theorem width_16025 : mW 16025 = 520946510935675 := by
  have hu : mW 16025 ≤ 520946510935675 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16025 ≤ 520946510935674 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16025 : RowArithmetic 16025 (1072848061756399358759/1000000000000000000000000) (147293975718925863369671/250000000000000000000000) (1029945531338159/200000000000000000000000) where
  r0 := (492950081457/1000000000000000000)
  k0 := (1659626036232557/500000000000000000)
  k6 := (2163374033191741/200000000000000000)
  q := (22378142237460195391/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16025]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16025]

theorem width_16026 : mW 16026 = 521060299080249 := by
  have hu : mW 16026 ≤ 521060299080249 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16026 ≤ 521060299080248 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16026 : RowArithmetic 16026 (268207011648824579201/250000000000000000000000) (117833438318070391325407/200000000000000000000000) (5148894753991057/1000000000000000000000000) where
  r0 := (246451971541/500000000000000000)
  k0 := (3319096733733849/1000000000000000000)
  k6 := (676033292619021/62500000000000000)
  q := (89515361810138487537/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16026]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16026]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 15952 then ⟨(1074320494248896824589/1000000000000000000000000), (589814702754751258659597/1000000000000000000000000), (2605520993762789/500000000000000000000000)⟩ else
  if n = 15953 then ⟨(1074300171980160233949/1000000000000000000000000), (58980591355604395498619/100000000000000000000000), (5210195186713331/1000000000000000000000000)⟩ else
  if n = 15954 then ⟨(1074279853959917540009/1000000000000000000000000), (147449281358039806763901/250000000000000000000000), (5209348578289883/1000000000000000000000000)⟩ else
  if n = 15955 then ⟨(107425954018700528333/100000000000000000000000), (589788338382887034460757/1000000000000000000000000), (1041700432439819/200000000000000000000000)⟩ else
  if n = 15956 then ⟨(1074239230660260685993/1000000000000000000000000), (589779552408017247222959/1000000000000000000000000), (5207655938384859/1000000000000000000000000)⟩ else
  if n = 15957 then ⟨(1074218925378521650913/1000000000000000000000000), (23590830700293594761371/40000000000000000000000), (2603404953395547/500000000000000000000000)⟩ else
  if n = 15958 then ⟨(537099312170312970727/500000000000000000000000), (29488099184032247022349/50000000000000000000000), (1301491016840431/250000000000000000000000)⟩ else
  if n = 15959 then ⟨(537089163772706137391/500000000000000000000000), (589753200927722618232379/1000000000000000000000000), (5205118420040709/1000000000000000000000000)⟩ else
  if n = 15960 then ⟨(134269754373964937697/125000000000000000000000), (589744419248363009110281/1000000000000000000000000), (650534120596503/125000000000000000000000)⟩ else
  if n = 15961 then ⟨(33566804583699572919/31250000000000000000000), (147433909660589099813581/250000000000000000000000), (130085692537491/25000000000000000000000)⟩ else
  if n = 15962 then ⟨(1074117462604252980571/1000000000000000000000000), (589726859109493043912871/1000000000000000000000000), (5202582630167591/1000000000000000000000000)⟩ else
  if n = 15963 then ⟨(1074097182768159240743/1000000000000000000000000), (294859040324781637324991/500000000000000000000000), (2600868875359951/500000000000000000000000)⟩ else
  if n = 15964 then ⟨(1074076907168945590853/1000000000000000000000000), (58970930326235743790581/100000000000000000000000), (1300223265775157/250000000000000000000000)⟩ else
  if n = 15965 then ⟨(537028317902726456927/500000000000000000000000), (589700526947666094743561/1000000000000000000000000), (2600024283626921/500000000000000000000000)⟩ else
  if n = 15966 then ⟨(537018184338260976833/500000000000000000000000), (589691751705279617757741/1000000000000000000000000), (259960213156181/50000000000000000000000)⟩ else
  if n = 15967 then ⟨(1074016105780994950019/1000000000000000000000000), (9213796523984198076109/15625000000000000000000), (5198360150654099/1000000000000000000000000)⟩ else
  if n = 15968 then ⟨(268498961779428296531/250000000000000000000000), (58967420443658381803487/100000000000000000000000), (5197516229789383/1000000000000000000000000)⟩ else
  if n = 15969 then ⟨(536987796342759856191/500000000000000000000000), (58966543240985575373113/100000000000000000000000), (5196672500473651/1000000000000000000000000)⟩ else
  if n = 15970 then ⟨(1073955342483256623293/1000000000000000000000000), (589656661454595200436863/1000000000000000000000000), (649478620331381/125000000000000000000000)⟩ else
  if n = 15971 then ⟨(214787019301953555839/200000000000000000000000), (589647891570592937854997/1000000000000000000000000), (81171650254153/15625000000000000000000)⟩ else
  if n = 15972 then ⟨(1073914854763896085147/1000000000000000000000000), (294819561378819895682619/500000000000000000000000), (5194142461262071/1000000000000000000000000)⟩ else
  if n = 15973 then ⟨(1073894617244485667193/1000000000000000000000000), (294815177507763355549093/500000000000000000000000), (5193299497584123/1000000000000000000000000)⟩ else
  if n = 15974 then ⟨(214774876790076211151/200000000000000000000000), (589621588344044613262581/1000000000000000000000000), (5192456725176207/1000000000000000000000000)⟩ else
  if n = 15975 then ⟨(134231769360053364237/125000000000000000000000), (589612822742984463957803/1000000000000000000000000), (519161414398259/100000000000000000000000)⟩ else
  if n = 15976 then ⟨(268458482508367009409/250000000000000000000000), (589604058212137417535697/1000000000000000000000000), (5190771753947553/1000000000000000000000000)⟩ else
  if n = 15977 then ⟨(1073813709408350170313/1000000000000000000000000), (147398823687823644146549/250000000000000000000000), (1037985911003083/200000000000000000000000)⟩ else
  if n = 15978 then ⟨(536896746501959593829/500000000000000000000000), (73698316545030883389179/125000000000000000000000), (1037817509426101/200000000000000000000000)⟩ else
  if n = 15979 then ⟨(134221660102377671157/125000000000000000000000), (589577771038786166618677/1000000000000000000000000), (207529829209487/40000000000000000000000)⟩ else
  if n = 15980 then ⟨(33554783526640731199/31250000000000000000000), (11791380215734063045917/20000000000000000000000), (5187404104279793/1000000000000000000000000)⟩ else
  if n = 15981 then ⟨(536866434551606045393/500000000000000000000000), (36847515725236834084817/62500000000000000000000), (5186562669202741/1000000000000000000000000)⟩ else
  if n = 15982 then ⟨(1073712669569995207723/1000000000000000000000000), (589551493489836213921711/1000000000000000000000000), (129643035623761/25000000000000000000000)⟩ else
  if n = 15983 then ⟨(214738494850340074321/200000000000000000000000), (589542736444635150934337/1000000000000000000000000), (5184880371467311/1000000000000000000000000)⟩ else
  if n = 15984 then ⟨(1073672283147175878853/1000000000000000000000000), (23581359218719107380963/40000000000000000000000), (2592019754348903/500000000000000000000000)⟩ else
  if n = 15985 then ⟨(1073652096255270428653/1000000000000000000000000), (589525225559655418972923/1000000000000000000000000), (5183198836586397/1000000000000000000000000)⟩ else
  if n = 15986 then ⟨(13420398919685407273/12500000000000000000000), (147379117929864988910797/250000000000000000000000), (1036471671015511/200000000000000000000000)⟩ else
  if n = 15987 then ⟨(214722347020942476779/200000000000000000000000), (294753859473591469794413/500000000000000000000000), (2590759032057907/500000000000000000000000)⟩ else
  if n = 15988 then ⟨(134198945105469866299/125000000000000000000000), (589498967242616162899759/1000000000000000000000000), (207227118545827/40000000000000000000000)⟩ else
  if n = 15989 then ⟨(1073571390790823070961/1000000000000000000000000), (73686277075693927733153/125000000000000000000000), (80934969587683/15625000000000000000000)⟩ else
  if n = 15990 then ⟨(134193903118094338243/125000000000000000000000), (589481467035780513882191/1000000000000000000000000), (5178998333958467/1000000000000000000000000)⟩ else
  if n = 15991 then ⟨(536765531652202609211/500000000000000000000000), (73684089816636917578617/125000000000000000000000), (323634925289409/62500000000000000000000)⟩ else
  if n = 15992 then ⟨(53675545293431292641/50000000000000000000000), (294731985548643977594773/500000000000000000000000), (2588659732786273/500000000000000000000000)⟩ else
  if n = 15993 then ⟨(214698150527253651053/200000000000000000000000), (589455224728150280735541/1000000000000000000000000), (2588240158364549/500000000000000000000000)⟩ else
  if n = 15994 then ⟨(536735301803092236699/500000000000000000000000), (589446479425474437419003/1000000000000000000000000), (2587820679022421/500000000000000000000000)⟩ else
  if n = 15995 then ⟨(1073450458777226956199/1000000000000000000000000), (589437735189052523043861/1000000000000000000000000), (5174802589464443/1000000000000000000000000)⟩ else
  if n = 15996 then ⟨(1073430318148248823281/1000000000000000000000000), (58942899201867671743539/100000000000000000000000), (1293491002733149/250000000000000000000000)⟩ else
  if n = 15997 then ⟨(134176272714762882009/125000000000000000000000), (117884049982827858315077/200000000000000000000000), (2586562811196997/500000000000000000000000)⟩ else
  if n = 15998 then ⟨(268347512371410893939/250000000000000000000000), (147352877218808134115621/250000000000000000000000), (1293071855948343/250000000000000000000000)⟩ else
  if n = 15999 then ⟨(1073369921449724165357/1000000000000000000000000), (147350692225437185751221/250000000000000000000000), (1034289883015093/200000000000000000000000)⟩ else
  if n = 16000 then ⟨(1073349797609199277813/1000000000000000000000000), (589394029993480415101617/1000000000000000000000000), (2585305798092519/500000000000000000000000)⟩ else
  if n = 16001 then ⟨(1073329677962924035303/1000000000000000000000000), (589385292150219909147681/1000000000000000000000000), (1033954793413377/200000000000000000000000)⟩ else
  if n = 16002 then ⟨(268327390627438288249/250000000000000000000000), (589376555371759838733273/1000000000000000000000000), (40382316622389/7812500000000000000000)⟩ else
  if n = 16003 then ⟨(1073289451248542553123/1000000000000000000000000), (294683909828946343822409/500000000000000000000000), (1033619855585319/200000000000000000000000)⟩ else
  if n = 16004 then ⟨(1073269344178148019831/1000000000000000000000000), (117871817001682235530191/200000000000000000000000), (5167262217794127/1000000000000000000000000)⟩ else
  if n = 16005 then ⟨(536624620648713002893/500000000000000000000000), (294675175711553950381249/500000000000000000000000), (645803168401657/125000000000000000000000)⟩ else
  if n = 16006 then ⟨(536614571302616681499/500000000000000000000000), (4714732951214205295499/8000000000000000000000), (2582794333064433/500000000000000000000000)⟩ else
  if n = 16007 then ⟨(268302262025106701457/250000000000000000000000), (58933288744420722902027/100000000000000000000000), (5164752174485843/1000000000000000000000000)⟩ else
  if n = 16008 then ⟨(1073188957781864253331/1000000000000000000000000), (2946620785250977127029/5000000000000000000000), (2581957936114561/500000000000000000000000)⟩ else
  if n = 16009 then ⟨(134146108956050435819/125000000000000000000000), (117863085543906642479809/200000000000000000000000), (5163079759303641/1000000000000000000000000)⟩ else
  if n = 16010 then ⟨(21462975793978053711/20000000000000000000000), (589306699452013522975973/1000000000000000000000000), (5162243835654353/1000000000000000000000000)⟩ else
  if n = 16011 then ⟨(536564355966110348617/500000000000000000000000), (147324493061857339722051/250000000000000000000000), (2580704050613123/500000000000000000000000)⟩ else
  if n = 16012 then ⟨(1073108638347216230939/1000000000000000000000000), (294644623052786903412757/500000000000000000000000), (1032114511192861/200000000000000000000000)⟩ else
  if n = 16013 then ⟨(107308856894274919833/100000000000000000000000), (589280521026240019328661/1000000000000000000000000), (2579868599906783/500000000000000000000000)⟩ else
  if n = 16014 then ⟨(268267125929419709421/250000000000000000000000), (117854359401844219991813/200000000000000000000000), (1031780406543809/200000000000000000000000)⟩ else
  if n = 16015 then ⟨(67065527666929116043/62500000000000000000000), (2301808883024649984607/3906250000000000000000), (2579033527312909/500000000000000000000000)⟩ else
  if n = 16016 then ⟨(214605677160234111517/200000000000000000000000), (117850870432260215318141/200000000000000000000000), (5157232265478951/1000000000000000000000000)⟩ else
  if n = 16017 then ⟨(1073008333107454175637/1000000000000000000000000), (589245631329986638204351/1000000000000000000000000), (103127953304471/20000000000000000000000)⟩ else
  if n = 16018 then ⟨(268247071147144452153/250000000000000000000000), (589236911560160340133831/1000000000000000000000000), (2577781626902361/500000000000000000000000)⟩ else
  if n = 16019 then ⟨(214593648048680643861/200000000000000000000000), (147307048212903928743599/250000000000000000000000), (2577364515583801/500000000000000000000000)⟩ else
  if n = 16020 then ⟨(536474100035396283863/500000000000000000000000), (589219475204146263881179/1000000000000000000000000), (2576947498628673/500000000000000000000000)⟩ else
  if n = 16021 then ⟨(268232041017402102731/250000000000000000000000), (147302689654386384397929/250000000000000000000000), (515306115201913/100000000000000000000000)⟩ else
  if n = 16022 then ⟨(536454066119356717927/500000000000000000000000), (294601021545803613875741/500000000000000000000000), (257611374769907/50000000000000000000000)⟩ else
  if n = 16023 then ⟨(1072888104576971260243/1000000000000000000000000), (147298332156531228758299/250000000000000000000000), (2575697013669801/500000000000000000000000)⟩ else
  if n = 16024 then ⟨(1072868081083245097663/1000000000000000000000000), (36824038451305774472609/62500000000000000000000), (1287640186947183/250000000000000000000000)⟩ else
  if n = 16025 then ⟨(1072848061756399358759/1000000000000000000000000), (147293975718925863369671/250000000000000000000000), (1029945531338159/200000000000000000000000)⟩ else
  ⟨(268207011648824579201/250000000000000000000000), (117833438318070391325407/200000000000000000000000), (5148894753991057/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15952 ≤ n) (hb : n ≤ 16026) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15952
  · exact row_15953
  · exact row_15954
  · exact row_15955
  · exact row_15956
  · exact row_15957
  · exact row_15958
  · exact row_15959
  · exact row_15960
  · exact row_15961
  · exact row_15962
  · exact row_15963
  · exact row_15964
  · exact row_15965
  · exact row_15966
  · exact row_15967
  · exact row_15968
  · exact row_15969
  · exact row_15970
  · exact row_15971
  · exact row_15972
  · exact row_15973
  · exact row_15974
  · exact row_15975
  · exact row_15976
  · exact row_15977
  · exact row_15978
  · exact row_15979
  · exact row_15980
  · exact row_15981
  · exact row_15982
  · exact row_15983
  · exact row_15984
  · exact row_15985
  · exact row_15986
  · exact row_15987
  · exact row_15988
  · exact row_15989
  · exact row_15990
  · exact row_15991
  · exact row_15992
  · exact row_15993
  · exact row_15994
  · exact row_15995
  · exact row_15996
  · exact row_15997
  · exact row_15998
  · exact row_15999
  · exact row_16000
  · exact row_16001
  · exact row_16002
  · exact row_16003
  · exact row_16004
  · exact row_16005
  · exact row_16006
  · exact row_16007
  · exact row_16008
  · exact row_16009
  · exact row_16010
  · exact row_16011
  · exact row_16012
  · exact row_16013
  · exact row_16014
  · exact row_16015
  · exact row_16016
  · exact row_16017
  · exact row_16018
  · exact row_16019
  · exact row_16020
  · exact row_16021
  · exact row_16022
  · exact row_16023
  · exact row_16024
  · exact row_16025
  · exact row_16026

end BstLean.Part271.R3.Rows15952
