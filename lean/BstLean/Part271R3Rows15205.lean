import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15205–15279. -/
namespace BstLean.Part271.R3.Rows15205
open Real BstLean.Part130 BstLean.Part227

theorem width_15205 : mW 15205 = 433463452393185 := by
  have hu : mW 15205 ≤ 433463452393185 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15205 ≤ 433463452393184 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15205 : RowArithmetic 15205 (272693692404410106529/250000000000000000000000) (298347974950265614886093/500000000000000000000000) (1475386344889569/250000000000000000000000) where
  r0 := (533359903179/1000000000000000000)
  k0 := (1726310649626151/500000000000000000)
  k6 := (5552357587370751/500000000000000000)
  q := (174384632350445376051/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15205]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15205]

theorem width_15206 : mW 15206 = 433563238437892 := by
  have hu : mW 15206 ≤ 433563238437892 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15206 ≤ 433563238437891 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15206 : RowArithmetic 15206 (272687729776473041971/250000000000000000000000) (298343147451133950797677/500000000000000000000000) (1475134417665723/250000000000000000000000) where
  r0 := (133326822653/250000000000000000)
  k0 := (345245100547107/100000000000000000)
  k6 := (11104350026189877/1000000000000000000)
  q := (174390366706421028731/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15206]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15206]

theorem width_15207 : mW 15207 = 433663040889651 := by
  have hu : mW 15207 ≤ 433663040889651 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15207 ≤ 433663040889650 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15207 : RowArithmetic 15207 (272681768458373643347/250000000000000000000000) (596676641153007253360063/1000000000000000000000000) (5899530202312631/1000000000000000000000000) where
  r0 := (266627343347/500000000000000000)
  k0 := (1726140365643167/500000000000000000)
  k6 := (11103984913656653/1000000000000000000)
  q := (87198050436922040167/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15207]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15207]

theorem width_15208 : mW 15208 = 433762859750080 := by
  have hu : mW 15208 ≤ 433762859750080 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15208 ≤ 433762859750079 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15208 : RowArithmetic 15208 (8521119014054225531/7812500000000000000000) (149166747163122754798717/250000000000000000000000) (2949261487216887/500000000000000000000000) where
  r0 := (533202091423/1000000000000000000)
  k0 := (1726055238347259/500000000000000000)
  k6 := (1110361983713591/100000000000000000)
  q := (174401834852733129151/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15208]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15208]

theorem width_15209 : mW 15209 = 433862695020796 := by
  have hu : mW 15209 ≤ 433862695020796 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15209 ≤ 433862695020795 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15209 : RowArithmetic 15209 (218135879800145038547/200000000000000000000000) (74582167175057631806883/125000000000000000000000) (5897515986952647/1000000000000000000000000) where
  r0 := (533149504797/1000000000000000000)
  k0 := (215746265105753/62500000000000000)
  k6 := (346976712394429/31250000000000000)
  q := (8720378432155338521/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15209]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15209]

theorem width_15210 : mW 15210 = 433962546703420 := by
  have hu : mW 15210 ≤ 433962546703420 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15210 ≤ 433962546703419 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15210 : RowArithmetic 15210 (545327784718670398697/500000000000000000000000) (14916192184916480298703/25000000000000000000000) (5896509239795547/1000000000000000000000000) where
  r0 := (106619385363/200000000000000000)
  k0 := (431471253284823/125000000000000000)
  k6 := (2775722448027047/250000000000000000)
  q := (1090083139031147477/6250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15210]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15210]

theorem width_15211 : mW 15211 = 434062414799569 := by
  have hu : mW 15211 ≤ 434062414799569 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15211 ≤ 434062414799568 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15211 : RowArithmetic 15211 (545315872553641465797/500000000000000000000000) (298319019320413722394113/500000000000000000000000) (1179100546577771/200000000000000000000000) where
  r0 := (533044357473/1000000000000000000)
  k0 := (3451599830444073/1000000000000000000)
  k6 := (5551262411794687/500000000000000000)
  q := (21802379457297774497/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15211]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15211]

theorem width_15212 : mW 15212 = 434162299310862 := by
  have hu : mW 15212 ≤ 434162299310862 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15212 ≤ 434162299310861 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15212 : RowArithmetic 15212 (1090607926009046676089/1000000000000000000000000) (3728927444579423819763/6250000000000000000000) (2947248233079477/500000000000000000000000) where
  r0 := (133247949193/250000000000000000)
  k0 := (69028593083893/20000000000000000)
  k6 := (1110215989105937/100000000000000000)
  q := (1362693506900946527/7812500000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15212]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15212]

theorem width_15213 : mW 15213 = 434262200238918 := by
  have hu : mW 15213 ≤ 434262200238918 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15213 ≤ 434262200238917 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15213 : RowArithmetic 15213 (1090584112141127665523/1000000000000000000000000) (596618744872042332580791/1000000000000000000000000) (5893490439532253/1000000000000000000000000) where
  r0 := (532939244707/1000000000000000000)
  k0 := (3451259497517023/1000000000000000000)
  k6 := (11101794994512261/1000000000000000000)
  q := (6977220076792762311/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15213]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15213]

theorem width_15214 : mW 15214 = 434362117585356 := by
  have hu : mW 15214 ≤ 434362117585356 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15214 ≤ 434362117585355 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15214 : RowArithmetic 15214 (1090560303502022088159/1000000000000000000000000) (4772872798868586345553/8000000000000000000000) (5892484652935191/1000000000000000000000000) where
  r0 := (266443350639/500000000000000000)
  k0 := (1725544680207043/500000000000000000)
  k6 := (2220286026788427/200000000000000000)
  q := (174436234767894482893/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15214]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15214]

theorem width_15215 : mW 15215 = 434462051351795 := by
  have hu : mW 15215 ≤ 434462051351795 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15215 ≤ 434462051351794 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15215 : RowArithmetic 15215 (1090536500090226685621/1000000000000000000000000) (298299728046021430449121/500000000000000000000000) (1178295821258847/200000000000000000000000) where
  r0 := (266417083241/500000000000000000)
  k0 := (3450919242879019/1000000000000000000)
  k6 := (277526632733577/25000000000000000)
  q := (87220983713783003859/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15215]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15215]

theorem width_15216 : mW 15216 = 434562001539854 := by
  have hu : mW 15216 ≤ 434562001539854 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15216 ≤ 434562001539853 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15216 : RowArithmetic 15216 (272628175476059688157/250000000000000000000000) (596589813572193405833127/1000000000000000000000000) (5890473799535879/1000000000000000000000000) where
  r0 := (266390820159/500000000000000000)
  k0 := (3450749144911479/1000000000000000000)
  k6 := (5550350260354593/500000000000000000)
  q := (34889539979770441221/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15216]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15216]

theorem width_15217 : mW 15217 = 434661968151150 := by
  have hu : mW 15217 ≤ 434661968151150 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15217 ≤ 434661968151149 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15217 : RowArithmetic 15217 (1090488908942556857289/1000000000000000000000000) (298290086149383639532357/500000000000000000000000) (5889468732586673/1000000000000000000000000) where
  r0 := (532729122783/1000000000000000000)
  k0 := (3450579066504643/1000000000000000000)
  k6 := (2220067153606909/200000000000000000)
  q := (87226716090885824429/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15217]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15217]

theorem width_15218 : mW 15218 = 434761951187305 := by
  have hu : mW 15218 ≤ 434761951187305 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15218 ≤ 434761951187304 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15218 : RowArithmetic 15218 (1090465121203678318477/1000000000000000000000000) (298285266135753497778629/500000000000000000000000) (5888463905373129/1000000000000000000000000) where
  r0 := (4261412911/8000000000000000)
  k0 := (1725204503827463/500000000000000000)
  k6 := (346874095353539/31250000000000000)
  q := (174459164276342903729/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15218]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15218]

theorem width_15219 : mW 15219 = 434861950649936 := by
  have hu : mW 15219 ≤ 434861950649936 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15219 ≤ 434861950649935 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15219 : RowArithmetic 15219 (1090441338686102809041/1000000000000000000000000) (596560893490155038056661/1000000000000000000000000) (5887459317821853/1000000000000000000000000) where
  r0 := (532624113593/1000000000000000000)
  k0 := (1725119484180991/500000000000000000)
  k6 := (1109960637053939/100000000000000000)
  q := (174464896182584535421/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15219]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15219]

theorem width_15220 : mW 15220 = 434961966540664 := by
  have hu : mW 15220 ≤ 434961966540664 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15220 ≤ 434961966540663 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15220 : RowArithmetic 15220 (34075548793385284791/31250000000000000000000) (149137813988613520991657/250000000000000000000000) (2943227484929713/500000000000000000000000) where
  r0 := (266285810967/500000000000000000)
  k0 := (431258618577373/125000000000000000)
  k6 := (2219848345141413/200000000000000000)
  q := (87235313950257552793/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15220]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15220]

theorem width_15221 : mW 15221 = 435061998861106 := by
  have hu : mW 15221 ≤ 435061998861106 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15221 ≤ 435061998861105 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15221 : RowArithmetic 15221 (545196894654429003707/500000000000000000000000) (149135404916036690210593/250000000000000000000000) (588545086141251/100000000000000000000000) where
  r0 := (532519138897/1000000000000000000)
  k0 := (215618684276599/62500000000000000)
  k6 := (2774719279202593/250000000000000000)
  q := (174476359430153172829/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15221]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15221]

theorem width_15222 : mW 15222 = 435162047612883 := by
  have hu : mW 15222 ≤ 435162047612883 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15222 ≤ 435162047612882 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15222 : RowArithmetic 15222 (109037002244618937953/100000000000000000000000) (14913299615474396868033/25000000000000000000000) (2942223496203871/500000000000000000000000) where
  r0 := (532466664479/1000000000000000000)
  k0 := (689945793554991/200000000000000000)
  k6 := (5549256271921703/500000000000000000)
  q := (87241045385758646353/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15222]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15222]

theorem width_15223 : mW 15223 = 435262112797613 := by
  have hu : mW 15223 ≤ 435262112797613 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15223 ≤ 435262112797612 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15223 : RowArithmetic 15223 (1090346260798824748561/1000000000000000000000000) (596522350818684216995007/1000000000000000000000000) (1470860840692957/250000000000000000000000) where
  r0 := (266207099339/500000000000000000)
  k0 := (215597437916469/62500000000000000)
  k6 := (11098148006800269/1000000000000000000)
  q := (43621955481156504431/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15223]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15223]

theorem width_15224 : mW 15224 = 435362194416916 := by
  have hu : mW 15224 ≤ 435362194416916 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15224 ≤ 435362194416915 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15224 : RowArithmetic 15224 (1090322504365265465221/1000000000000000000000000) (298256359131507368482501/500000000000000000000000) (2941219986215737/500000000000000000000000) where
  r0 := (532361741493/1000000000000000000)
  k0 := (3449389065090883/1000000000000000000)
  k6 := (554889175283753/50000000000000000)
  q := (87246776444748948673/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15224]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15224]

theorem width_15225 : mW 15225 = 435462292472411 := by
  have hu : mW 15225 ≤ 435462292472411 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15225 ≤ 435462292472410 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15225 : RowArithmetic 15225 (545149376572006895343/500000000000000000000000) (298251543475855209734431/500000000000000000000000) (5881436821313429/1000000000000000000000000) where
  r0 := (266154646461/500000000000000000)
  k0 := (3449219143053497/1000000000000000000)
  k6 := (5548709520230941/500000000000000000)
  q := (174499283666151477987/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15225]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15225]

theorem width_15226 : mW 15226 = 435562406965719 := by
  have hu : mW 15226 ≤ 435562406965719 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15226 ≤ 435562406965718 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15226 : RowArithmetic 15226 (545137503566785909263/500000000000000000000000) (596493456884514230228931/1000000000000000000000000) (5880433909344443/1000000000000000000000000) where
  r0 := (266128426481/500000000000000000)
  k0 := (862262310136129/250000000000000000)
  k6 := (5548527305577419/500000000000000000)
  q := (87252507127302651509/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15226]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15226]

theorem width_15227 : mW 15227 = 435662537898458 := by
  have hu : mW 15227 ≤ 435662537898458 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15227 ≤ 435662537898457 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15227 : RowArithmetic 15227 (43610050653297730813/40000000000000000000000) (119296765612233868004219/200000000000000000000000) (5879431236451333/1000000000000000000000000) where
  r0 := (133051105403/250000000000000000)
  k0 := (689775871512717/200000000000000000)
  k6 := (11096690217748033/1000000000000000000)
  q := (43627686163719478191/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15227]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15227]

theorem width_15228 : mW 15228 = 435762685272247 := by
  have hu : mW 15228 ≤ 435762685272247 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15228 ≤ 435762685272246 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15228 : RowArithmetic 15228 (545113765369566029153/500000000000000000000000) (2329977345630542925649/3906250000000000000000) (5878428802560931/1000000000000000000000000) where
  r0 := (532151998869/1000000000000000000)
  k0 := (3448709494103867/1000000000000000000)
  k6 := (2774081465058893/250000000000000000)
  q := (174516474866987844507/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15228]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15228]

theorem width_15229 : mW 15229 = 435862849088708 := by
  have hu : mW 15229 ≤ 435862849088708 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15229 ≤ 435862849088707 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15229 : RowArithmetic 15229 (136275475044017696061/125000000000000000000000) (74558071768125803819837/125000000000000000000000) (2938713303800029/500000000000000000000000) where
  r0 := (133024896183/250000000000000000)
  k0 := (3448539650165009/1000000000000000000)
  k6 := (2773990384652891/250000000000000000)
  q := (87261102445476816243/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15229]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15229]

theorem width_15230 : mW 15230 = 435963029349458 := by
  have hu : mW 15230 ≤ 435963029349458 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15230 ≤ 435963029349457 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15230 : RowArithmetic 15230 (545090037584988765213/500000000000000000000000) (59645494905167494194267/100000000000000000000000) (587642465149563/100000000000000000000000) where
  r0 := (532047179199/1000000000000000000)
  k0 := (3448369825743413/1000000000000000000)
  k6 := (11095597252870117/1000000000000000000)
  q := (34905586945358761579/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15230]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15230]

theorem width_15231 : mW 15231 = 436063226056119 := by
  have hu : mW 15231 ≤ 436063226056119 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15231 ≤ 436063226056118 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15231 : RowArithmetic 15231 (1090156355191144429967/1000000000000000000000000) (59644532520116802881333/100000000000000000000000) (2937711467087261/500000000000000000000000) where
  r0 := (531994782267/1000000000000000000)
  k0 := (3448200020832239/1000000000000000000)
  k6 := (5547616501502671/500000000000000000)
  q := (174533664374526898891/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15231]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15231]

theorem width_15232 : mW 15232 = 436163439210309 := by
  have hu : mW 15232 ≤ 436163439210309 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15232 ≤ 436163439210308 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15232 : RowArithmetic 15232 (545066320207074368189/500000000000000000000000) (596435702593229117330963/1000000000000000000000000) (2937210727781847/500000000000000000000000) where
  r0 := (265971196967/500000000000000000)
  k0 := (3448030235427889/1000000000000000000)
  k6 := (11094868789011349/1000000000000000000)
  q := (34907878766834286117/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15232]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15232]

theorem width_15233 : mW 15233 = 436263668813649 := by
  have hu : mW 15233 ≤ 436263668813649 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15233 ≤ 436263668813648 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15233 : RowArithmetic 15233 (545054465418748196391/500000000000000000000000) (596426081227601813553399/1000000000000000000000000) (5873420215590089/1000000000000000000000000) where
  r0 := (2659450071/5000000000000000)
  k0 := (861965117383311/250000000000000000)
  k6 := (2773626152720563/250000000000000000)
  q := (174545123105745925049/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15233]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15233]

theorem width_15234 : mW 15234 = 436363914867758 := by
  have hu : mW 15234 ≤ 436363914867758 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15234 ≤ 436363914867757 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15234 : RowArithmetic 15234 (218017045291938921533/200000000000000000000000) (5964164611040296881363/10000000000000000000000) (587241921418071/100000000000000000000000) where
  r0 := (531837643061/1000000000000000000)
  k0 := (1723845361569111/500000000000000000)
  k6 := (5547070234306083/500000000000000000)
  q := (87275426094634450659/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15234]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15234]

theorem width_15235 : mW 15235 = 436464177374257 := by
  have hu : mW 15235 ≤ 436464177374257 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15235 ≤ 436464177374256 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15235 : RowArithmetic 15235 (136257690909906302753/125000000000000000000000) (372754276388910307283/625000000000000000000) (2935709225631279/500000000000000000000000) where
  r0 := (132946320129/250000000000000000)
  k0 := (172376049812123/50000000000000000)
  k6 := (2773444090548801/250000000000000000)
  q := (21819572635594859423/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15235]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15235]

theorem width_15236 : mW 15236 = 436564456334765 := by
  have hu : mW 15236 ≤ 436564456334765 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15236 ≤ 436564456334764 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15236 : RowArithmetic 15236 (34063682290458504411/31250000000000000000000) (37274826536376626734917/62500000000000000000000) (587041792676269/100000000000000000000000) where
  r0 := (531732926563/1000000000000000000)
  k0 := (861837822210589/250000000000000000)
  k6 := (5546706145812743/500000000000000000)
  q := (43640577448058590051/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15236]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15236]

theorem width_15237 : mW 15237 = 436664751750902 := by
  have hu : mW 15237 ≤ 436664751750902 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15237 ≤ 436664751750901 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15237 : RowArithmetic 15237 (1090014144504468260411/1000000000000000000000000) (119277521636616413540361/200000000000000000000000) (366838602538011/62500000000000000000000) where
  r0 := (531680581199/1000000000000000000)
  k0 := (430897700116383/125000000000000000)
  k6 := (1386631032112141/125000000000000000)
  q := (174568038311713865693/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15237]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15237]

theorem width_15238 : mW 15238 = 436765063624289 := by
  have hu : mW 15238 ≤ 436765063624289 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15238 ≤ 436765063624288 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15238 : RowArithmetic 15238 (544995230453573732827/500000000000000000000000) (59637799302516859486463/100000000000000000000000) (2934208796363051/500000000000000000000000) where
  r0 := (66453530553/125000000000000000)
  k0 := (1723505966255731/500000000000000000)
  k6 := (11092684258004251/1000000000000000000)
  q := (34914753328643179747/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15238]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15238]

theorem width_15239 : mW 15239 = 436865391956546 := by
  have hu : mW 15239 ≤ 436865391956546 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15239 ≤ 436865391956545 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15239 : RowArithmetic 15239 (1089966782501219348171/1000000000000000000000000) (596368379108029613446931/1000000000000000000000000) (1466854445760899/250000000000000000000000) where
  r0 := (265787958117/500000000000000000)
  k0 := (172342114178673/50000000000000000)
  k6 := (443692811797639/40000000000000000)
  q := (43644873696689740793/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15239]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15239]

theorem width_15240 : mW 15240 = 436965736749292 := by
  have hu : mW 15240 ≤ 436965736749292 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15240 ≤ 436965736749291 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15240 : RowArithmetic 15240 (1089943109285194403743/1000000000000000000000000) (596358766431409171705747/1000000000000000000000000) (2933209105743913/500000000000000000000000) where
  r0 := (132880899157/250000000000000000)
  k0 := (861668163529173/250000000000000000)
  k6 := (11091956367701423/1000000000000000000)
  q := (34917044548472311963/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15240]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15240]

theorem width_15241 : mW 15241 = 437066098004149 := by
  have hu : mW 15241 ≤ 437066098004149 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15241 ≤ 437066098004148 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15241 : RowArithmetic 15241 (1089919441257582603751/1000000000000000000000000) (596349154995051416713303/1000000000000000000000000) (5865418877985947/1000000000000000000000000) where
  r0 := (132867821401/250000000000000000)
  k0 := (3446503044137551/1000000000000000000)
  k6 := (5545796238139859/500000000000000000)
  q := (43647737627510546609/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15241]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15241]

theorem width_15242 : mW 15242 = 437166475722737 := by
  have hu : mW 15242 ≤ 437166475722737 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15242 ≤ 437166475722736 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15242 : RowArithmetic 15242 (544947889208447590609/500000000000000000000000) (596339544798700520491919/1000000000000000000000000) (5864419782465171/1000000000000000000000000) where
  r0 := (13285474579/25000000000000000)
  k0 := (1723166726816213/500000000000000000)
  k6 := (5545614310334993/500000000000000000)
  q := (174596678089819337777/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15242]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15242]

theorem width_15243 : mW 15243 = 437266869906675 := by
  have hu : mW 15243 ≤ 437266869906675 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15243 ≤ 437266869906674 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15243 : RowArithmetic 15243 (544936060380822136237/500000000000000000000000) (596329935842100836356499/1000000000000000000000000) (5863420924852749/1000000000000000000000000) where
  r0 := (265683344647/500000000000000000)
  k0 := (3446163882597707/1000000000000000000)
  k6 := (11090864800866353/1000000000000000000)
  q := (174602405481711505543/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15243]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15243]

theorem width_15244 : mW 15244 = 437367280557584 := by
  have hu : mW 15244 ≤ 437367280557584 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15244 ≤ 437367280557583 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15244 : RowArithmetic 15244 (43593938731613673859/40000000000000000000000) (74540041015624582690851/125000000000000000000000) (2931211152537967/500000000000000000000000) where
  r0 := (132828601001/250000000000000000)
  k0 := (3445994331029783/1000000000000000000)
  k6 := (11090501016862947/1000000000000000000)
  q := (174608132685737178409/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15244]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15244]

theorem width_15245 : mW 15245 = 437467707677085 := by
  have hu : mW 15245 ≤ 437467707677085 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15245 ≤ 437467707677084 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15245 : RowArithmetic 15245 (108982482100150041879/100000000000000000000000) (596310721647132475967361/1000000000000000000000000) (732677990382751/125000000000000000000000) where
  r0 := (66407765911/125000000000000000)
  k0 := (1722912399462521/500000000000000000)
  k6 := (1386267158581737/125000000000000000)
  q := (5456683115684838813/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15245]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15245]

theorem width_15246 : mW 15246 = 437568151266798 := by
  have hu : mW 15246 ≤ 437568151266798 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15246 ≤ 437568151266797 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15246 : RowArithmetic 15246 (1089801178893633407653/1000000000000000000000000) (596301116408252786051557/1000000000000000000000000) (1465106444684573/250000000000000000000000) where
  r0 := (66401232393/125000000000000000)
  k0 := (3445655286279869/1000000000000000000)
  k6 := (2772443389058333/250000000000000000)
  q := (87309793265131489487/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15246]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15246]

theorem width_15247 : mW 15247 = 437668611328345 := by
  have hu : mW 15247 ≤ 437668611328345 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15247 ≤ 437668611328344 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15247 : RowArithmetic 15247 (544888770982627032253/500000000000000000000000) (29814575620405105273053/50000000000000000000000) (5859427872032111/1000000000000000000000000) where
  r0 := (53115759957/100000000000000000)
  k0 := (68909715861813/20000000000000000)
  k6 := (5544704939797693/500000000000000000)
  q := (87312656585400034431/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15247]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15247]

theorem width_15248 : mW 15248 = 437769087863344 := by
  have hu : mW 15248 ≤ 437769087863344 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15248 ≤ 437769087863343 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15248 : RowArithmetic 15248 (1089753910214877611319/1000000000000000000000000) (74535238705803143895991/125000000000000000000000) (5858430202870867/1000000000000000000000000) where
  r0 := (132776337141/250000000000000000)
  k0 := (3445316319353769/1000000000000000000)
  k6 := (11089046238734191/1000000000000000000)
  q := (174631039623544588231/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15248]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15248]

theorem width_15249 : mW 15249 = 437869580873418 := by
  have hu : mW 15249 ≤ 437869580873418 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15249 ≤ 437869580873417 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15249 : RowArithmetic 15249 (136216285455127254313/125000000000000000000000) (596272308122966585522991/1000000000000000000000000) (732179096397741/125000000000000000000000) where
  r0 := (132763276531/250000000000000000)
  k0 := (344514686506561/100000000000000000)
  k6 := (11088682633643881/1000000000000000000)
  q := (174636765888515010601/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15249]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15249]

theorem width_15250 : mW 15250 = 437970090360187 := by
  have hu : mW 15250 ≤ 437970090360187 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15250 ≤ 437970090360186 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15250 : RowArithmetic 15250 (34053333195068466693/31250000000000000000000) (119252541567494261903219/200000000000000000000000) (2928217788446363/500000000000000000000000) where
  r0 := (531000872249/1000000000000000000)
  k0 := (17224887151129/5000000000000000)
  k6 := (11088319064318593/1000000000000000000)
  q := (1364394468482264113/7812500000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15250]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15250]

theorem width_15251 : mW 15251 = 438070616325271 := by
  have hu : mW 15251 ≤ 438070616325271 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15251 ≤ 438070616325270 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15251 : RowArithmetic 15251 (136210380752114056871/125000000000000000000000) (23850124351587361002609/40000000000000000000000) (2927719309965361/500000000000000000000000) where
  r0 := (66368580867/125000000000000000)
  k0 := (1722404007413737/500000000000000000)
  k6 := (692997220672029/62500000000000000)
  q := (87324108927603721641/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15251]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15251]

theorem width_15252 : mW 15252 = 438171158770292 := by
  have hu : mW 15252 ≤ 438171158770292 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15252 ≤ 438171158770291 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15252 : RowArithmetic 15252 (1089659434963698574783/1000000000000000000000000) (596243510979349777315621/1000000000000000000000000) (5854441900223379/1000000000000000000000000) where
  r0 := (530896430183/1000000000000000000)
  k0 := (688927723773403/200000000000000000)
  k6 := (11087592032939631/1000000000000000000)
  q := (87326971778483192747/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15252]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15252]

theorem width_15253 : mW 15253 = 438271717696871 := by
  have hu : mW 15253 ≤ 438271717696871 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15253 ≤ 438271717696870 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15253 : RowArithmetic 15253 (272408957270266542993/250000000000000000000000) (119246782881242713136903/200000000000000000000000) (29267227088491/5000000000000000000000) where
  r0 := (132711055497/250000000000000000)
  k0 := (2152793276463/625000000000000)
  k6 := (2771807142718559/250000000000000000)
  q := (174659669071025094509/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15253]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15253]

theorem width_15254 : mW 15254 = 438372293106627 := by
  have hu : mW 15254 ≤ 438372293106627 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15254 ≤ 438372293106626 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15254 : RowArithmetic 15254 (1089612228367533379613/1000000000000000000000000) (14905607976750511206229/25000000000000000000000) (731556146535343/125000000000000000000000) where
  r0 := (10615840447/20000000000000000)
  k0 := (3444299885248453/1000000000000000000)
  k6 := (11086865144550419/1000000000000000000)
  q := (174665394397402028711/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15254]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15254]

theorem width_15255 : mW 15255 = 438472885001184 := by
  have hu : mW 15255 ≤ 438472885001184 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15255 ≤ 438472885001183 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15255 : RowArithmetic 15255 (544794316410808549147/500000000000000000000000) (298107362485257806382677/500000000000000000000000) (365715822744033/62500000000000000000000) where
  r0 := (265369915633/500000000000000000)
  k0 := (1722065273791553/500000000000000000)
  k6 := (5543250876981161/500000000000000000)
  q := (174671119536115643459/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15255]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15255]

theorem width_15256 : mW 15256 = 438573493382160 := by
  have hu : mW 15256 ≤ 438573493382160 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15256 ≤ 438573493382159 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15256 : RowArithmetic 15256 (1089565042441836903707/1000000000000000000000000) (149051283026861065723919/250000000000000000000000) (292522869624559/50000000000000000000000) where
  r0 := (265343824367/500000000000000000)
  k0 := (688792245868227/200000000000000000)
  k6 := (1108613839910409/100000000000000000)
  q := (174676844487184391089/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15256]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15256]

theorem width_15257 : mW 15257 = 438674118251178 := by
  have hu : mW 15257 ≤ 438674118251178 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15257 ≤ 438674118251177 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15257 : RowArithmetic 15257 (1089541457226711139351/1000000000000000000000000) (298097770240275834295543/500000000000000000000000) (2924730928985143/500000000000000000000000) where
  r0 := (530635474753/1000000000000000000)
  k0 := (3443791930522161/1000000000000000000)
  k6 := (11085775079969869/1000000000000000000)
  q := (17468256925062672091/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15257]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15257]

theorem width_15258 : mW 15258 = 438774759609859 := by
  have hu : mW 15258 ≤ 438774759609859 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15258 ≤ 438774759609858 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15258 : RowArithmetic 15258 (1089517877174759402421/1000000000000000000000000) (4769487600716665915681/8000000000000000000000) (584846656026949/100000000000000000000000) where
  r0 := (530583309321/1000000000000000000)
  k0 := (1721811325561279/500000000000000000)
  k6 := (11085411796553803/1000000000000000000)
  q := (43672073456615269803/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15258]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15258]

theorem width_15259 : mW 15259 = 438875417459824 := by
  have hu : mW 15259 ≤ 438875417459824 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15259 ≤ 438875417459823 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15259 : RowArithmetic 15259 (1089494302284501833109/1000000000000000000000000) (596176360934284389483789/1000000000000000000000000) (5847471499316461/1000000000000000000000000) where
  r0 := (106106230487/200000000000000000)
  k0 := (3443453391135453/1000000000000000000)
  k6 := (5542524274425021/500000000000000000)
  q := (8734700910735295463/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15259]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15259]

theorem width_15260 : mW 15260 = 438976091802694 := by
  have hu : mW 15260 ≤ 438976091802694 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15260 ≤ 438976091802693 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15260 : RowArithmetic 15260 (272367683138614778587/250000000000000000000000) (149041693253600159624969/250000000000000000000000) (365404792189931/62500000000000000000000) where
  r0 := (530479004093/1000000000000000000)
  k0 := (172164207527861/50000000000000000)
  k6 := (5542342668426367/500000000000000000)
  q := (87349871207689825649/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15260]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15260]

theorem width_15261 : mW 15261 = 439076782640090 := by
  have hu : mW 15261 ≤ 439076782640090 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15261 ≤ 439076782640089 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15261 : RowArithmetic 15261 (1089447167983152471549/1000000000000000000000000) (119231437265935523908589/200000000000000000000000) (146137052184113/25000000000000000000000) where
  r0 := (265213432147/500000000000000000)
  k0 := (3443114929387473/1000000000000000000)
  k6 := (11084322160556031/1000000000000000000)
  q := (43676366607125185637/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15261]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15261]

theorem width_15262 : mW 15262 = 439177489973635 := by
  have hu : mW 15262 ≤ 439177489973635 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15262 ≤ 439177489973634 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15262 : RowArithmetic 15262 (272355902142275741017/250000000000000000000000) (596147600879860915387399/1000000000000000000000000) (5844487736221059/1000000000000000000000000) where
  r0 := (132593683259/250000000000000000)
  k0 := (430368215952823/125000000000000000)
  k6 := (2770989754988521/250000000000000000)
  q := (87355595127043808607/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15262]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15262]

theorem width_15263 : mW 15263 = 439278213804948 := by
  have hu : mW 15263 ≤ 439278213804948 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15263 ≤ 439278213804947 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15263 : RowArithmetic 15263 (108940005431083361033/100000000000000000000000) (298069008332348155248831/500000000000000000000000) (18260917567301/3125000000000000000000) where
  r0 := (530322610317/1000000000000000000)
  k0 := (3442776545258921/1000000000000000000)
  k6 := (11083595915041047/1000000000000000000)
  q := (174716913892158706479/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15263]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15263]

theorem width_15264 : mW 15264 = 439378954135653 := by
  have hu : mW 15264 ≤ 439378954135653 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15264 ≤ 439378954135652 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15264 : RowArithmetic 15264 (1089376505206866200039/1000000000000000000000000) (596128433683929589009549/1000000000000000000000000) (730312467904759/125000000000000000000000) where
  r0 := (265135248067/500000000000000000)
  k0 := (3442607382289607/1000000000000000000)
  k6 := (11083232845811073/1000000000000000000)
  q := (174722637342732438507/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15264]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15264]

theorem width_15265 : mW 15265 = 439479710967370 := by
  have hu : mW 15265 ≤ 439479710967370 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15265 ≤ 439479710967369 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15265 : RowArithmetic 15265 (68084560078482780057/62500000000000000000000) (596118851937306614425377/1000000000000000000000000) (5841506101254163/1000000000000000000000000) where
  r0 := (265109195243/500000000000000000)
  k0 := (688487647742851/200000000000000000)
  k6 := (138535872653229/12500000000000000)
  q := (43682090151456809611/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15265]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15265]

theorem width_15266 : mW 15266 = 439580484301721 := by
  have hu : mW 15266 ≤ 439580484301721 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15266 ≤ 439580484301720 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15266 : RowArithmetic 15266 (1089329422455932034123/1000000000000000000000000) (18628414732017916319383/31250000000000000000000) (5840512695512443/1000000000000000000000000) where
  r0 := (53016629337/100000000000000000)
  k0 := (107570909828937/31250000000000000)
  k6 := (692656675898559/62500000000000000)
  q := (87367041840730764209/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15266]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15266]

theorem width_15267 : mW 15267 = 439681274140327 := by
  have hu : mW 15267 ≤ 439681274140327 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15267 ≤ 439681274140326 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15267 : RowArithmetic 15267 (1089305888806013335791/1000000000000000000000000) (596099692145475805299489/1000000000000000000000000) (2919759762970401/500000000000000000000000) where
  r0 := (265057102393/500000000000000000)
  k0 := (860525002431913/250000000000000000)
  k6 := (692633990760069/62500000000000000)
  q := (87369903284826863771/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15267]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15267]

theorem width_15268 : mW 15268 = 439782080484811 := by
  have hu : mW 15268 ≤ 439782080484811 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15268 ≤ 439782080484810 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15268 : RowArithmetic 15268 (544641180152246348029/500000000000000000000000) (596090114099760050058737/1000000000000000000000000) (5838526592467133/1000000000000000000000000) where
  r0 := (530062124731/1000000000000000000)
  k0 := (3441930924312377/1000000000000000000)
  k6 := (69261130785031/6250000000000000)
  q := (174745529270422251911/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15268]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15268]

theorem width_15269 : mW 15269 = 439882903336793 := by
  have hu : mW 15269 ≤ 439882903336793 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15269 ≤ 439882903336792 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15269 : RowArithmetic 15269 (1089258836949896026159/1000000000000000000000000) (596080537287172254949011/1000000000000000000000000) (2918766947509697/500000000000000000000000) where
  r0 := (265005026601/500000000000000000)
  k0 := (1720880929136637/500000000000000000)
  k6 := (11081418034702673/1000000000000000000)
  q := (34950250356757102921/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15269]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15269]

theorem width_15270 : mW 15270 = 439983742697897 := by
  have hu : mW 15270 ≤ 439983742697897 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15270 ≤ 439983742697896 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15270 : RowArithmetic 15270 (544617659370374182357/500000000000000000000000) (596070961707458665244199/1000000000000000000000000) (72956767919069/12500000000000000000000) where
  r0 := (529957990199/1000000000000000000)
  k0 := (8603982029033/2500000000000000)
  k6 := (11081055179448407/1000000000000000000)
  q := (17475697410976192569/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15270]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15270]

theorem width_15271 : mW 15271 = 440084598569743 := by
  have hu : mW 15271 ≤ 440084598569743 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15271 ≤ 440084598569742 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15271 : RowArithmetic 15271 (544605902837788351793/500000000000000000000000) (596061387360365595121967/1000000000000000000000000) (233421968316541/40000000000000000000000) where
  r0 := (264952967859/500000000000000000)
  k0 := (3441423784322021/1000000000000000000)
  k6 := (2770173089959081/250000000000000000)
  q := (87381348124184946109/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15271]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15271]

theorem width_15272 : mW 15272 = 440185470953954 := by
  have hu : mW 15272 ≤ 440185470953954 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15272 ≤ 440185470953953 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15272 : RowArithmetic 15272 (1089188297752907515379/1000000000000000000000000) (298025907122819697691049/500000000000000000000000) (5834557218111409/1000000000000000000000000) where
  r0 := (529853889759/1000000000000000000)
  k0 := (107539211762581/31250000000000000)
  k6 := (11080329575860591/1000000000000000000)
  q := (87384209099813909113/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15272]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15272]

theorem width_15273 : mW 15273 = 440286359852151 := by
  have hu : mW 15273 ≤ 440286359852151 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15273 ≤ 440286359852150 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15273 : RowArithmetic 15273 (1089164794971268518493/1000000000000000000000000) (14901056059075662987379/25000000000000000000000) (5833565464047231/1000000000000000000000000) where
  r0 := (264900926159/500000000000000000)
  k0 := (430135723480597/125000000000000000)
  k6 := (5539983413757687/500000000000000000)
  q := (8738706998177705237/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15273]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15273]

theorem width_15274 : mW 15274 = 440387265265957 := by
  have hu : mW 15274 ≤ 440387265265957 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15274 ≤ 440387265265956 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15274 : RowArithmetic 15274 (1089141297329187265431/1000000000000000000000000) (149008167928068380968057/250000000000000000000000) (2916286972824523/500000000000000000000000) where
  r0 := (105949964679/200000000000000000)
  k0 := (1720458409325713/500000000000000000)
  k6 := (11079604114794841/1000000000000000000)
  q := (87389930770083574887/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15274]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15274]

theorem width_15275 : mW 15275 = 440488187196993 := by
  have hu : mW 15275 ≤ 440488187196993 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15275 ≤ 440488187196992 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15275 : RowArithmetic 15275 (1089117804825192553441/1000000000000000000000000) (14900577557328173340911/25000000000000000000000) (1166316532568993/200000000000000000000000) where
  r0 := (132424450747/250000000000000000)
  k0 := (34407478688189/10000000000000000)
  k6 := (11079241437693161/1000000000000000000)
  q := (174785582929485348329/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15275]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15275]

theorem width_15276 : mW 15276 = 440589125646882 := by
  have hu : mW 15276 ≤ 440589125646882 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15276 ≤ 440589125646881 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15276 : RowArithmetic 15276 (1089094317457813013899/1000000000000000000000000) (596013534105333444414821/1000000000000000000000000) (5830591615563101/1000000000000000000000000) where
  r0 := (529645791093/1000000000000000000)
  k0 := (3440578938337057/1000000000000000000)
  k6 := (5539439398102253/500000000000000000)
  q := (174791304131527092397/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15276]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15276]

theorem width_15277 : mW 15277 = 440690080617246 := by
  have hu : mW 15277 ≤ 440690080617246 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15277 ≤ 440690080617245 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15277 : RowArithmetic 15277 (1089070835225578169759/1000000000000000000000000) (298001983574319892717831/500000000000000000000000) (2914800401865803/500000000000000000000000) where
  r0 := (52959378771/100000000000000000)
  k0 := (3440410027208749/1000000000000000000)
  k6 := (5539258095161523/500000000000000000)
  q := (174797025146310770961/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15277]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15277]

theorem width_15278 : mW 15278 = 440791052109708 := by
  have hu : mW 15278 ≤ 440791052109708 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15278 ≤ 440791052109707 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15278 : RowArithmetic 15278 (272261839531754432663/250000000000000000000000) (29799720071139639873563/50000000000000000000000) (728576278409831/125000000000000000000000) where
  r0 := (132385448209/250000000000000000)
  k0 := (86006028385677/25000000000000000)
  k6 := (2769538405010739/250000000000000000)
  q := (21850343246731846249/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15278]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15278]

theorem width_15279 : mW 15279 = 440892040125888 := by
  have hu : mW 15279 ≤ 440892040125888 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15279 ≤ 440892040125887 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15279 : RowArithmetic 15279 (272255971540165750179/250000000000000000000000) (595984836927539291516317/1000000000000000000000000) (5827619886132459/1000000000000000000000000) where
  r0 := (52948980647/100000000000000000)
  k0 := (860018065747913/250000000000000000)
  k6 := (11077791085358411/1000000000000000000)
  q := (87404233307088736227/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15279]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15279]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 15205 then ⟨(272693692404410106529/250000000000000000000000), (298347974950265614886093/500000000000000000000000), (1475386344889569/250000000000000000000000)⟩ else
  if n = 15206 then ⟨(272687729776473041971/250000000000000000000000), (298343147451133950797677/500000000000000000000000), (1475134417665723/250000000000000000000000)⟩ else
  if n = 15207 then ⟨(272681768458373643347/250000000000000000000000), (596676641153007253360063/1000000000000000000000000), (5899530202312631/1000000000000000000000000)⟩ else
  if n = 15208 then ⟨(8521119014054225531/7812500000000000000000), (149166747163122754798717/250000000000000000000000), (2949261487216887/500000000000000000000000)⟩ else
  if n = 15209 then ⟨(218135879800145038547/200000000000000000000000), (74582167175057631806883/125000000000000000000000), (5897515986952647/1000000000000000000000000)⟩ else
  if n = 15210 then ⟨(545327784718670398697/500000000000000000000000), (14916192184916480298703/25000000000000000000000), (5896509239795547/1000000000000000000000000)⟩ else
  if n = 15211 then ⟨(545315872553641465797/500000000000000000000000), (298319019320413722394113/500000000000000000000000), (1179100546577771/200000000000000000000000)⟩ else
  if n = 15212 then ⟨(1090607926009046676089/1000000000000000000000000), (3728927444579423819763/6250000000000000000000), (2947248233079477/500000000000000000000000)⟩ else
  if n = 15213 then ⟨(1090584112141127665523/1000000000000000000000000), (596618744872042332580791/1000000000000000000000000), (5893490439532253/1000000000000000000000000)⟩ else
  if n = 15214 then ⟨(1090560303502022088159/1000000000000000000000000), (4772872798868586345553/8000000000000000000000), (5892484652935191/1000000000000000000000000)⟩ else
  if n = 15215 then ⟨(1090536500090226685621/1000000000000000000000000), (298299728046021430449121/500000000000000000000000), (1178295821258847/200000000000000000000000)⟩ else
  if n = 15216 then ⟨(272628175476059688157/250000000000000000000000), (596589813572193405833127/1000000000000000000000000), (5890473799535879/1000000000000000000000000)⟩ else
  if n = 15217 then ⟨(1090488908942556857289/1000000000000000000000000), (298290086149383639532357/500000000000000000000000), (5889468732586673/1000000000000000000000000)⟩ else
  if n = 15218 then ⟨(1090465121203678318477/1000000000000000000000000), (298285266135753497778629/500000000000000000000000), (5888463905373129/1000000000000000000000000)⟩ else
  if n = 15219 then ⟨(1090441338686102809041/1000000000000000000000000), (596560893490155038056661/1000000000000000000000000), (5887459317821853/1000000000000000000000000)⟩ else
  if n = 15220 then ⟨(34075548793385284791/31250000000000000000000), (149137813988613520991657/250000000000000000000000), (2943227484929713/500000000000000000000000)⟩ else
  if n = 15221 then ⟨(545196894654429003707/500000000000000000000000), (149135404916036690210593/250000000000000000000000), (588545086141251/100000000000000000000000)⟩ else
  if n = 15222 then ⟨(109037002244618937953/100000000000000000000000), (14913299615474396868033/25000000000000000000000), (2942223496203871/500000000000000000000000)⟩ else
  if n = 15223 then ⟨(1090346260798824748561/1000000000000000000000000), (596522350818684216995007/1000000000000000000000000), (1470860840692957/250000000000000000000000)⟩ else
  if n = 15224 then ⟨(1090322504365265465221/1000000000000000000000000), (298256359131507368482501/500000000000000000000000), (2941219986215737/500000000000000000000000)⟩ else
  if n = 15225 then ⟨(545149376572006895343/500000000000000000000000), (298251543475855209734431/500000000000000000000000), (5881436821313429/1000000000000000000000000)⟩ else
  if n = 15226 then ⟨(545137503566785909263/500000000000000000000000), (596493456884514230228931/1000000000000000000000000), (5880433909344443/1000000000000000000000000)⟩ else
  if n = 15227 then ⟨(43610050653297730813/40000000000000000000000), (119296765612233868004219/200000000000000000000000), (5879431236451333/1000000000000000000000000)⟩ else
  if n = 15228 then ⟨(545113765369566029153/500000000000000000000000), (2329977345630542925649/3906250000000000000000), (5878428802560931/1000000000000000000000000)⟩ else
  if n = 15229 then ⟨(136275475044017696061/125000000000000000000000), (74558071768125803819837/125000000000000000000000), (2938713303800029/500000000000000000000000)⟩ else
  if n = 15230 then ⟨(545090037584988765213/500000000000000000000000), (59645494905167494194267/100000000000000000000000), (587642465149563/100000000000000000000000)⟩ else
  if n = 15231 then ⟨(1090156355191144429967/1000000000000000000000000), (59644532520116802881333/100000000000000000000000), (2937711467087261/500000000000000000000000)⟩ else
  if n = 15232 then ⟨(545066320207074368189/500000000000000000000000), (596435702593229117330963/1000000000000000000000000), (2937210727781847/500000000000000000000000)⟩ else
  if n = 15233 then ⟨(545054465418748196391/500000000000000000000000), (596426081227601813553399/1000000000000000000000000), (5873420215590089/1000000000000000000000000)⟩ else
  if n = 15234 then ⟨(218017045291938921533/200000000000000000000000), (5964164611040296881363/10000000000000000000000), (587241921418071/100000000000000000000000)⟩ else
  if n = 15235 then ⟨(136257690909906302753/125000000000000000000000), (372754276388910307283/625000000000000000000), (2935709225631279/500000000000000000000000)⟩ else
  if n = 15236 then ⟨(34063682290458504411/31250000000000000000000), (37274826536376626734917/62500000000000000000000), (587041792676269/100000000000000000000000)⟩ else
  if n = 15237 then ⟨(1090014144504468260411/1000000000000000000000000), (119277521636616413540361/200000000000000000000000), (366838602538011/62500000000000000000000)⟩ else
  if n = 15238 then ⟨(544995230453573732827/500000000000000000000000), (59637799302516859486463/100000000000000000000000), (2934208796363051/500000000000000000000000)⟩ else
  if n = 15239 then ⟨(1089966782501219348171/1000000000000000000000000), (596368379108029613446931/1000000000000000000000000), (1466854445760899/250000000000000000000000)⟩ else
  if n = 15240 then ⟨(1089943109285194403743/1000000000000000000000000), (596358766431409171705747/1000000000000000000000000), (2933209105743913/500000000000000000000000)⟩ else
  if n = 15241 then ⟨(1089919441257582603751/1000000000000000000000000), (596349154995051416713303/1000000000000000000000000), (5865418877985947/1000000000000000000000000)⟩ else
  if n = 15242 then ⟨(544947889208447590609/500000000000000000000000), (596339544798700520491919/1000000000000000000000000), (5864419782465171/1000000000000000000000000)⟩ else
  if n = 15243 then ⟨(544936060380822136237/500000000000000000000000), (596329935842100836356499/1000000000000000000000000), (5863420924852749/1000000000000000000000000)⟩ else
  if n = 15244 then ⟨(43593938731613673859/40000000000000000000000), (74540041015624582690851/125000000000000000000000), (2931211152537967/500000000000000000000000)⟩ else
  if n = 15245 then ⟨(108982482100150041879/100000000000000000000000), (596310721647132475967361/1000000000000000000000000), (732677990382751/125000000000000000000000)⟩ else
  if n = 15246 then ⟨(1089801178893633407653/1000000000000000000000000), (596301116408252786051557/1000000000000000000000000), (1465106444684573/250000000000000000000000)⟩ else
  if n = 15247 then ⟨(544888770982627032253/500000000000000000000000), (29814575620405105273053/50000000000000000000000), (5859427872032111/1000000000000000000000000)⟩ else
  if n = 15248 then ⟨(1089753910214877611319/1000000000000000000000000), (74535238705803143895991/125000000000000000000000), (5858430202870867/1000000000000000000000000)⟩ else
  if n = 15249 then ⟨(136216285455127254313/125000000000000000000000), (596272308122966585522991/1000000000000000000000000), (732179096397741/125000000000000000000000)⟩ else
  if n = 15250 then ⟨(34053333195068466693/31250000000000000000000), (119252541567494261903219/200000000000000000000000), (2928217788446363/500000000000000000000000)⟩ else
  if n = 15251 then ⟨(136210380752114056871/125000000000000000000000), (23850124351587361002609/40000000000000000000000), (2927719309965361/500000000000000000000000)⟩ else
  if n = 15252 then ⟨(1089659434963698574783/1000000000000000000000000), (596243510979349777315621/1000000000000000000000000), (5854441900223379/1000000000000000000000000)⟩ else
  if n = 15253 then ⟨(272408957270266542993/250000000000000000000000), (119246782881242713136903/200000000000000000000000), (29267227088491/5000000000000000000000)⟩ else
  if n = 15254 then ⟨(1089612228367533379613/1000000000000000000000000), (14905607976750511206229/25000000000000000000000), (731556146535343/125000000000000000000000)⟩ else
  if n = 15255 then ⟨(544794316410808549147/500000000000000000000000), (298107362485257806382677/500000000000000000000000), (365715822744033/62500000000000000000000)⟩ else
  if n = 15256 then ⟨(1089565042441836903707/1000000000000000000000000), (149051283026861065723919/250000000000000000000000), (292522869624559/50000000000000000000000)⟩ else
  if n = 15257 then ⟨(1089541457226711139351/1000000000000000000000000), (298097770240275834295543/500000000000000000000000), (2924730928985143/500000000000000000000000)⟩ else
  if n = 15258 then ⟨(1089517877174759402421/1000000000000000000000000), (4769487600716665915681/8000000000000000000000), (584846656026949/100000000000000000000000)⟩ else
  if n = 15259 then ⟨(1089494302284501833109/1000000000000000000000000), (596176360934284389483789/1000000000000000000000000), (5847471499316461/1000000000000000000000000)⟩ else
  if n = 15260 then ⟨(272367683138614778587/250000000000000000000000), (149041693253600159624969/250000000000000000000000), (365404792189931/62500000000000000000000)⟩ else
  if n = 15261 then ⟨(1089447167983152471549/1000000000000000000000000), (119231437265935523908589/200000000000000000000000), (146137052184113/25000000000000000000000)⟩ else
  if n = 15262 then ⟨(272355902142275741017/250000000000000000000000), (596147600879860915387399/1000000000000000000000000), (5844487736221059/1000000000000000000000000)⟩ else
  if n = 15263 then ⟨(108940005431083361033/100000000000000000000000), (298069008332348155248831/500000000000000000000000), (18260917567301/3125000000000000000000)⟩ else
  if n = 15264 then ⟨(1089376505206866200039/1000000000000000000000000), (596128433683929589009549/1000000000000000000000000), (730312467904759/125000000000000000000000)⟩ else
  if n = 15265 then ⟨(68084560078482780057/62500000000000000000000), (596118851937306614425377/1000000000000000000000000), (5841506101254163/1000000000000000000000000)⟩ else
  if n = 15266 then ⟨(1089329422455932034123/1000000000000000000000000), (18628414732017916319383/31250000000000000000000), (5840512695512443/1000000000000000000000000)⟩ else
  if n = 15267 then ⟨(1089305888806013335791/1000000000000000000000000), (596099692145475805299489/1000000000000000000000000), (2919759762970401/500000000000000000000000)⟩ else
  if n = 15268 then ⟨(544641180152246348029/500000000000000000000000), (596090114099760050058737/1000000000000000000000000), (5838526592467133/1000000000000000000000000)⟩ else
  if n = 15269 then ⟨(1089258836949896026159/1000000000000000000000000), (596080537287172254949011/1000000000000000000000000), (2918766947509697/500000000000000000000000)⟩ else
  if n = 15270 then ⟨(544617659370374182357/500000000000000000000000), (596070961707458665244199/1000000000000000000000000), (72956767919069/12500000000000000000000)⟩ else
  if n = 15271 then ⟨(544605902837788351793/500000000000000000000000), (596061387360365595121967/1000000000000000000000000), (233421968316541/40000000000000000000000)⟩ else
  if n = 15272 then ⟨(1089188297752907515379/1000000000000000000000000), (298025907122819697691049/500000000000000000000000), (5834557218111409/1000000000000000000000000)⟩ else
  if n = 15273 then ⟨(1089164794971268518493/1000000000000000000000000), (14901056059075662987379/25000000000000000000000), (5833565464047231/1000000000000000000000000)⟩ else
  if n = 15274 then ⟨(1089141297329187265431/1000000000000000000000000), (149008167928068380968057/250000000000000000000000), (2916286972824523/500000000000000000000000)⟩ else
  if n = 15275 then ⟨(1089117804825192553441/1000000000000000000000000), (14900577557328173340911/25000000000000000000000), (1166316532568993/200000000000000000000000)⟩ else
  if n = 15276 then ⟨(1089094317457813013899/1000000000000000000000000), (596013534105333444414821/1000000000000000000000000), (5830591615563101/1000000000000000000000000)⟩ else
  if n = 15277 then ⟨(1089070835225578169759/1000000000000000000000000), (298001983574319892717831/500000000000000000000000), (2914800401865803/500000000000000000000000)⟩ else
  if n = 15278 then ⟨(272261839531754432663/250000000000000000000000), (29799720071139639873563/50000000000000000000000), (728576278409831/125000000000000000000000)⟩ else
  ⟨(272255971540165750179/250000000000000000000000), (595984836927539291516317/1000000000000000000000000), (5827619886132459/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15205 ≤ n) (hb : n ≤ 15279) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15205
  · exact row_15206
  · exact row_15207
  · exact row_15208
  · exact row_15209
  · exact row_15210
  · exact row_15211
  · exact row_15212
  · exact row_15213
  · exact row_15214
  · exact row_15215
  · exact row_15216
  · exact row_15217
  · exact row_15218
  · exact row_15219
  · exact row_15220
  · exact row_15221
  · exact row_15222
  · exact row_15223
  · exact row_15224
  · exact row_15225
  · exact row_15226
  · exact row_15227
  · exact row_15228
  · exact row_15229
  · exact row_15230
  · exact row_15231
  · exact row_15232
  · exact row_15233
  · exact row_15234
  · exact row_15235
  · exact row_15236
  · exact row_15237
  · exact row_15238
  · exact row_15239
  · exact row_15240
  · exact row_15241
  · exact row_15242
  · exact row_15243
  · exact row_15244
  · exact row_15245
  · exact row_15246
  · exact row_15247
  · exact row_15248
  · exact row_15249
  · exact row_15250
  · exact row_15251
  · exact row_15252
  · exact row_15253
  · exact row_15254
  · exact row_15255
  · exact row_15256
  · exact row_15257
  · exact row_15258
  · exact row_15259
  · exact row_15260
  · exact row_15261
  · exact row_15262
  · exact row_15263
  · exact row_15264
  · exact row_15265
  · exact row_15266
  · exact row_15267
  · exact row_15268
  · exact row_15269
  · exact row_15270
  · exact row_15271
  · exact row_15272
  · exact row_15273
  · exact row_15274
  · exact row_15275
  · exact row_15276
  · exact row_15277
  · exact row_15278
  · exact row_15279

end BstLean.Part271.R3.Rows15205
