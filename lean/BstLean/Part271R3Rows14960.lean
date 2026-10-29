import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14960–15034. -/
namespace BstLean.Part271.R3.Rows14960
open Real BstLean.Part130 BstLean.Part227

theorem width_14960 : mW 14960 = 409506290430217 := by
  have hu : mW 14960 ≤ 409506290430217 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14960 ≤ 409506290430216 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14960 : RowArithmetic 14960 (274194963977140145179/250000000000000000000000) (599099715443160393394491/1000000000000000000000000) (6155870143670719/1000000000000000000000000) where
  r0 := (546515658563/1000000000000000000)
  k0 := (436867846309153/125000000000000000)
  k6 := (5597638443998739/500000000000000000)
  q := (172973986483517226013/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14960]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14960]

theorem width_14961 : mW 14961 = 409602105388719 := by
  have hu : mW 14961 ≤ 409602105388719 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14961 ≤ 409602105388718 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14961 : RowArithmetic 14961 (1096754674979481478061/1000000000000000000000000) (599089746470321769917097/1000000000000000000000000) (1230960241834837/200000000000000000000000) where
  r0 := (68307608181/125000000000000000)
  k0 := (139790702653719/40000000000000000)
  k6 := (279872568326559/25000000000000000)
  q := (86489883801517504409/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14961]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14961]

theorem width_14962 : mW 14962 = 409697936359348 := by
  have hu : mW 14962 ≤ 409697936359348 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14962 ≤ 409697936359347 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14962 : RowArithmetic 14962 (548364749837836052467/500000000000000000000000) (299539889406019013107899/500000000000000000000000) (1538433133536911/250000000000000000000000) where
  r0 := (546406081489/1000000000000000000)
  k0 := (436824047838471/125000000000000000)
  k6 := (11194528615638389/1000000000000000000)
  q := (43246387132337424887/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14962]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14962]

theorem width_14963 : mW 14963 = 409793783343707 := by
  have hu : mW 14963 ≤ 409793783343707 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14963 ≤ 409793783343706 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14963 : RowArithmetic 14963 (1096704329995488172493/1000000000000000000000000) (599069812468032070243613/1000000000000000000000000) (6152664118510269/1000000000000000000000000) where
  r0 := (546351306683/1000000000000000000)
  k0 := (3494417219561089/1000000000000000000)
  k6 := (5597077267859649/500000000000000000)
  q := (172991329262480667257/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14963]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14963]

theorem width_14964 : mW 14964 = 409889646343403 := by
  have hu : mW 14964 ≤ 409889646343403 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14964 ≤ 409889646343402 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14964 : RowArithmetic 14964 (274169791484321104333/250000000000000000000000) (599059847438026889475463/1000000000000000000000000) (3075797981090601/500000000000000000000000) where
  r0 := (546296541027/1000000000000000000)
  k0 := (3494242076896427/1000000000000000000)
  k6 := (11193780493298821/1000000000000000000)
  q := (43249277450611819441/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14964]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14964]

theorem width_14965 : mW 14965 = 409985525360040 := by
  have hu : mW 14965 ≤ 409985525360040 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14965 ≤ 409985525360039 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14965 : RowArithmetic 14965 (1096654007499417383599/1000000000000000000000000) (299524941860872836740831/500000000000000000000000) (3075264032539831/500000000000000000000000) where
  r0 := (13656044613/25000000000000000)
  k0 := (1747033477356831/500000000000000000)
  k6 := (2798351622092673/250000000000000000)
  q := (43250722537317223413/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14965]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14965]

theorem width_14966 : mW 14966 = 410081420395225 := by
  have hu : mW 14966 ≤ 410081420395225 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14966 ≤ 410081420395224 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14966 : RowArithmetic 14966 (274157213670060759757/250000000000000000000000) (299519960659455751289449/500000000000000000000000) (1229892085424971/200000000000000000000000) where
  r0 := (13654675929/25000000000000000)
  k0 := (1746945926504739/500000000000000000)
  k6 := (223860650418573/20000000000000000)
  q := (17300867030296487427/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14966]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14966]

theorem width_14967 : mW 14967 = 410177331450564 := by
  have hu : mW 14967 ≤ 410177331450564 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14967 ≤ 410177331450563 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14967 : RowArithmetic 14967 (109660370747811836391/100000000000000000000000) (299514980114623870064489/500000000000000000000000) (6148393048236033/1000000000000000000000000) where
  r0 := (109226459789/200000000000000000)
  k0 := (3493716771780557/1000000000000000000)
  k6 := (349770580967701/31250000000000000)
  q := (173014450263554575733/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14967]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14967]

theorem width_14968 : mW 14968 = 410273258527661 := by
  have hu : mW 14968 ≤ 410273258527661 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14968 ≤ 410273258527660 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14968 : RowArithmetic 14968 (1096578565891401746611/1000000000000000000000000) (599020000452477654983469/1000000000000000000000000) (614732592833251/100000000000000000000000) where
  r0 := (34129848117/62500000000000000)
  k0 := (174677085551019/50000000000000000)
  k6 := (5596142349238889/500000000000000000)
  q := (173020230031057350921/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14968]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14968]

theorem width_14969 : mW 14969 = 410369201628123 := by
  have hu : mW 14969 ≤ 410369201628123 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14969 ≤ 410369201628122 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14969 : RowArithmetic 14969 (43862137196738039983/40000000000000000000000) (299505020994162363415943/500000000000000000000000) (6146259067333587/1000000000000000000000000) where
  r0 := (546022849939/1000000000000000000)
  k0 := (3493366670725627/1000000000000000000)
  k6 := (1119191084345643/100000000000000000)
  q := (86513004802746274743/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14969]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14969]

theorem width_14970 : mW 14970 = 410465160753555 := by
  have hu : mW 14970 ≤ 410465160753555 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14970 ≤ 410465160753554 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14970 : RowArithmetic 14970 (1096528299557625342729/1000000000000000000000000) (599000084836512417509571/1000000000000000000000000) (192037264536207/31250000000000000000000) where
  r0 := (68246017393/125000000000000000)
  k0 := (3493191650892977/1000000000000000000)
  k6 := (11191537025896131/1000000000000000000)
  q := (43257947246719879461/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14970]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14970]

theorem width_14971 : mW 14971 = 410561135905564 := by
  have hu : mW 14971 ≤ 410561135905564 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14971 ≤ 410561135905563 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14971 : RowArithmetic 14971 (1096503174807283817149/1000000000000000000000000) (598990128996764337633849/1000000000000000000000000) (6144126121726987/1000000000000000000000000) where
  r0 := (272956718743/500000000000000000)
  k0 := (1746508325761153/500000000000000000)
  k6 := (3581172238653/320000000000000)
  q := (173037568175237599183/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14971]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14971]

theorem width_14972 : mW 14972 = 410657127085754 := by
  have hu : mW 14972 ≤ 410657127085754 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14972 ≤ 410657127085753 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14972 : RowArithmetic 14972 (274119513916446816537/250000000000000000000000) (59898017446880410514409/100000000000000000000000) (6143060036958113/1000000000000000000000000) where
  r0 := (545858744961/1000000000000000000)
  k0 := (873210418150973/250000000000000000)
  k6 := (11190789503133657/1000000000000000000)
  q := (173043347170586133459/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14972]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14972]

theorem width_14973 : mW 14973 = 410753134295733 := by
  have hu : mW 14973 ≤ 410753134295733 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14973 ≤ 410753134295732 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14973 : RowArithmetic 14973 (109645294213149556197/100000000000000000000000) (149742555313088879759737/250000000000000000000000) (1228398842154283/200000000000000000000000) where
  r0 := (4264094231/7812500000000000)
  k0 := (3492666714137609/1000000000000000000)
  k6 := (447616631916759/40000000000000000)
  q := (173049125972944457401/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14973]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14973]

theorem width_14974 : mW 14974 = 410849157537106 := by
  have hu : mW 14974 ≤ 410849157537106 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14974 ≤ 410849157537105 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14974 : RowArithmetic 14974 (548213917101385189097/500000000000000000000000) (598960269347142378395489/1000000000000000000000000) (307046432154319/50000000000000000000000) where
  r0 := (68218673413/125000000000000000)
  k0 := (873122944029233/250000000000000000)
  k6 := (1398755266267541/125000000000000000)
  q := (173054904582331904507/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14974]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14974]

theorem width_14975 : mW 14975 = 410945196811479 := by
  have hu : mW 14975 ≤ 410945196811479 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14975 ≤ 410945196811478 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14975 : RowArithmetic 14975 (1096402731877973605103/1000000000000000000000000) (598950318752888565901061/1000000000000000000000000) (383741458363907/62500000000000000000000) where
  r0 := (68211840271/125000000000000000)
  k0 := (1746158429270867/500000000000000000)
  k6 := (5594834249895733/500000000000000000)
  q := (21632585374845975631/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14975]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14975]

theorem width_14976 : mW 14976 = 411041252120458 := by
  have hu : mW 14976 ≤ 411041252120458 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14976 ≤ 411041252120457 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14976 : RowArithmetic 14976 (109637763515546774551/100000000000000000000000) (119788073893863627953693/200000000000000000000000) (3069399141449673/500000000000000000000000) where
  r0 := (545640066157/1000000000000000000)
  k0 := (1746070980702743/500000000000000000)
  k6 := (11189294906866139/1000000000000000000)
  q := (17306646122227148607/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14976]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14976]

theorem width_14977 : mW 14977 = 411137323465650 := by
  have hu : mW 14977 ≤ 411137323465650 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14977 ≤ 411137323465649 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14977 : RowArithmetic 14977 (34261017001050484977/31250000000000000000000) (598930421496155076762763/1000000000000000000000000) (3068866745118217/500000000000000000000000) where
  r0 := (545585419269/1000000000000000000)
  k0 := (3491967084704859/1000000000000000000)
  k6 := (5594460675679051/500000000000000000)
  q := (17307223925286227139/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14977]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14977]

theorem width_14978 : mW 14978 = 411233410848660 := by
  have hu : mW 14978 ≤ 411233410848660 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14978 ≤ 411233410848659 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14978 : RowArithmetic 14978 (548163729255390524429/500000000000000000000000) (299460237416561769670961/500000000000000000000000) (6136668955753391/1000000000000000000000000) where
  r0 := (272765390751/500000000000000000)
  k0 := (872948057109131/250000000000000000)
  k6 := (11188547833261109/1000000000000000000)
  q := (173078017090559481601/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14978]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14978]

theorem width_14979 : mW 14979 = 411329514271095 := by
  have hu : mW 14979 ≤ 411329514271095 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14979 ≤ 411329514271094 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14979 : RowArithmetic 14979 (548151189292664139013/500000000000000000000000) (299455264739973881669817/500000000000000000000000) (6135604679369829/1000000000000000000000000) where
  r0 := (109095230571/200000000000000000)
  k0 := (872904348150087/250000000000000000)
  k6 := (2797043588142229/250000000000000000)
  q := (173083794735382434069/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14979]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14979]

theorem width_14980 : mW 14980 = 411425633734561 := by
  have hu : mW 14980 ≤ 411425633734561 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14980 ≤ 411425633734560 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14980 : RowArithmetic 14980 (1096277304255622157207/1000000000000000000000000) (598900585436352065612069/1000000000000000000000000) (6134540661005409/1000000000000000000000000) where
  r0 := (136355383331/250000000000000000)
  k0 := (3491442577186599/1000000000000000000)
  k6 := (139847511365941/12500000000000000)
  q := (8654478609367522147/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14980]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14980]

theorem width_14981 : mW 14981 = 411521769240665 := by
  have hu : mW 14981 ≤ 411521769240665 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14981 ≤ 411521769240664 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14981 : RowArithmetic 14981 (1096252235520027853303/1000000000000000000000000) (299445321351030405664093/500000000000000000000000) (6133476900579811/1000000000000000000000000) where
  r0 := (545366922907/1000000000000000000)
  k0 := (436408472773993/125000000000000000)
  k6 := (279685687584349/25000000000000000)
  q := (173095349446482819133/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14981]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14981]

theorem width_14982 : mW 14982 = 411617920791013 := by
  have hu : mW 14982 ≤ 411617920791013 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14982 ≤ 411617920791012 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14982 : RowArithmetic 14982 (548113586188455769509/500000000000000000000000) (9357510957449976142869/15625000000000000000000) (1226482679602551/200000000000000000000000) where
  r0 := (136328080401/250000000000000000)
  k0 := (436386625952431/125000000000000000)
  k6 := (11187054134858717/1000000000000000000)
  q := (173101126512798870347/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14982]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14982]

theorem width_14983 : mW 14983 = 411714088387212 := by
  have hu : mW 14983 ≤ 411714088387212 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14983 ≤ 411714088387211 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14983 : RowArithmetic 14983 (1096202114824639603239/1000000000000000000000000) (598870761160289545440587/1000000000000000000000000) (383209384576499/62500000000000000000000) where
  r0 := (54525772941/100000000000000000)
  k0 := (1745459126728087/500000000000000000)
  k6 := (699167550232707/62500000000000000)
  q := (173106903386317901057/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14983]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14983]

theorem width_14984 : mW 14984 = 411810272030867 := by
  have hu : mW 14984 ≤ 411810272030867 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14984 ≤ 411810272030866 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14984 : RowArithmetic 14984 (548088531430789916943/500000000000000000000000) (149715205588064683697097/250000000000000000000000) (383142947883331/62500000000000000000000) where
  r0 := (21808125853/40000000000000000)
  k0 := (1745371759852593/500000000000000000)
  k6 := (11186307509961509/1000000000000000000)
  q := (173112680067059212519/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14984]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14984]

theorem width_14985 : mW 14985 = 411906471723587 := by
  have hu : mW 14985 ≤ 411906471723587 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14985 ≤ 411906471723586 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14985 : RowArithmetic 14985 (274038004121524763061/250000000000000000000000) (598850884852430650091021/1000000000000000000000000) (3064612218330233/500000000000000000000000) where
  r0 := (272574286173/500000000000000000)
  k0 := (3490568806359947/1000000000000000000)
  k6 := (349560445423971/31250000000000000)
  q := (173118456555042102767/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14985]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14985]

theorem width_14986 : mW 14986 = 412002687466976 := by
  have hu : mW 14986 ≤ 412002687466976 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14986 ≤ 412002687466975 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14986 : RowArithmetic 14986 (219225395139313332023/200000000000000000000000) (37427559291283132660631/62500000000000000000000) (1532040491181343/250000000000000000000000) where
  r0 := (545094007471/1000000000000000000)
  k0 := (872598528354279/250000000000000000)
  k6 := (1398195129316721/125000000000000000)
  q := (173124232850285866617/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14986]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14986]

theorem width_14987 : mW 14987 = 412098919262643 := by
  have hu : mW 14987 ≤ 412098919262643 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14987 ≤ 412098919262642 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14987 : RowArithmetic 14987 (1096101940491350699021/1000000000000000000000000) (598831013776282006893349/1000000000000000000000000) (6127099750247849/1000000000000000000000000) where
  r0 := (272519725849/500000000000000000)
  k0 := (3490219440873353/1000000000000000000)
  k6 := (2796296963213841/250000000000000000)
  q := (86565004476404897833/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14987]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14987]

theorem width_14988 : mW 14988 = 412195167112193 := by
  have hu : mW 14988 ≤ 412195167112193 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14988 ≤ 412195167112192 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14988 : RowArithmetic 14988 (137009613858602674421/125000000000000000000000) (598821080199411219126043/1000000000000000000000000) (3063018896573911/500000000000000000000000) where
  r0 := (21799396201/40000000000000000)
  k0 := (3490044788725319/1000000000000000000)
  k6 := (11184814708525629/1000000000000000000)
  q := (43283946215658294573/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14988]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14988]

theorem width_14989 : mW 14989 = 412291431017234 := by
  have hu : mW 14989 ≤ 412291431017234 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14989 ≤ 412291431017233 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14989 : RowArithmetic 14989 (27401297170683710089/25000000000000000000000) (9356424186400668481509/15625000000000000000000) (1224995218669041/200000000000000000000000) where
  r0 := (544930367449/1000000000000000000)
  k0 := (3489870156966467/1000000000000000000)
  k6 := (5592220800769167/500000000000000000)
  q := (173141560579775299657/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14989]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14989]

theorem width_14990 : mW 14990 = 412387710979372 := by
  have hu : mW 14990 ≤ 412387710979372 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14990 ≤ 412387710979371 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14990 : RowArithmetic 14990 (548013434182651387021/500000000000000000000000) (23952048678668073503129/40000000000000000000000) (612391465075997/100000000000000000000000) where
  r0 := (544875838969/1000000000000000000)
  k0 := (1744847772798329/500000000000000000)
  k6 := (11184068531887251/1000000000000000000)
  q := (34629467220851088341/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14990]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14990]

theorem width_14991 : mW 14991 = 412484007000215 := by
  have hu : mW 14991 ≤ 412484007000215 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14991 ≤ 412484007000214 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14991 : RowArithmetic 14991 (274000463870263844813/250000000000000000000000) (119758257462062701878167/200000000000000000000000) (6122853465312093/1000000000000000000000000) where
  r0 := (272410659791/500000000000000000)
  k0 := (3489520954609343/1000000000000000000)
  k6 := (11183695499566153/1000000000000000000)
  q := (34630622287218576633/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14991]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14991]

theorem width_14992 : mW 14992 = 412580319081369 := by
  have hu : mW 14992 ≤ 412580319081369 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14992 ≤ 412580319081368 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14992 : RowArithmetic 14992 (1095976848172978486471/1000000000000000000000000) (299390679480101535704659/500000000000000000000000) (612179253692161/100000000000000000000000) where
  r0 := (272383404643/500000000000000000)
  k0 := (3489346384001179/1000000000000000000)
  k6 := (2236664500913763/200000000000000000)
  q := (5411215205478340611/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14992]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14992]

theorem width_14993 : mW 14993 = 412676647224441 := by
  have hu : mW 14993 ≤ 412676647224441 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14993 ≤ 412676647224440 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14993 : RowArithmetic 14993 (1095951846439444577751/1000000000000000000000000) (299385715958047934300489/500000000000000000000000) (1530182966377143/250000000000000000000000) where
  r0 := (6808903851/12500000000000000)
  k0 := (174458591688601/50000000000000000)
  k6 := (5591474773444507/500000000000000000)
  q := (86582330760958381583/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14993]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14993]

theorem width_14994 : mW 14994 = 412772991431039 := by
  have hu : mW 14994 ≤ 412772991431039 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14994 ≤ 412772991431038 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14994 : RowArithmetic 14994 (1095926850278826350379/1000000000000000000000000) (598761506177717300042961/1000000000000000000000000) (6119671450993049/1000000000000000000000000) where
  r0 := (13616445399/25000000000000000)
  k0 := (1744498651956057/500000000000000000)
  k6 := (11182576626520527/1000000000000000000)
  q := (173170436275941743093/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14994]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14994]

theorem width_14995 : mW 14995 = 412869351702769 := by
  have hu : mW 14995 ≤ 412869351702769 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14995 ≤ 412869351702768 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14995 : RowArithmetic 14995 (34246933115296809209/31250000000000000000000) (299375790872396432400823/500000000000000000000000) (6118611293295169/1000000000000000000000000) where
  r0 := (272301666463/500000000000000000)
  k0 := (1744411397212259/500000000000000000)
  k6 := (5591101871728567/500000000000000000)
  q := (86588105418700552603/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14995]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14995]

theorem width_14996 : mW 14996 = 412965728041239 := by
  have hu : mW 14996 ≤ 412965728041239 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14996 ≤ 412965728041238 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14996 : RowArithmetic 14996 (1095876874669833123067/1000000000000000000000000) (299370829308524067622241/500000000000000000000000) (764693924041883/125000000000000000000000) where
  r0 := (272274429487/500000000000000000)
  k0 := (872162076324869/250000000000000000)
  k6 := (2236366179538523/200000000000000000)
  q := (21647748150789264021/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14996]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14996]

theorem width_14997 : mW 14997 = 413062120448056 := by
  have hu : mW 14997 ≤ 413062120448056 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14997 ≤ 413062120448055 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14997 : RowArithmetic 14997 (109585189521820694761/100000000000000000000000) (598731736794208782034597/1000000000000000000000000) (6116491748032909/1000000000000000000000000) where
  r0 := (544494394103/1000000000000000000)
  k0 := (3488473836536839/1000000000000000000)
  k6 := (11181458089220753/1000000000000000000)
  q := (173187759382700023429/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14997]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14997]

theorem width_14998 : mW 14998 = 413158528924827 := by
  have hu : mW 14998 ≤ 413158528924827 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14998 ≤ 413158528924826 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14998 : RowArithmetic 14998 (1095826921332994887077/1000000000000000000000000) (598721816276000490247507/1000000000000000000000000) (6115432360308913/1000000000000000000000000) where
  r0 := (54443993831/100000000000000000)
  k0 := (3488299388130053/1000000000000000000)
  k6 := (11181085318035331/1000000000000000000)
  q := (43298383341644523807/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14998]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14998]

theorem width_14999 : mW 14999 = 413254953473160 := by
  have hu : mW 14999 ≤ 413254953473160 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14999 ≤ 413254953473159 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14999 : RowArithmetic 14999 (27395048825314316869/25000000000000000000000) (598711897062149102210131/1000000000000000000000000) (6114373229083299/1000000000000000000000000) where
  r0 := (272192745797/500000000000000000)
  k0 := (436015620009871/125000000000000000)
  k6 := (5590356292065067/500000000000000000)
  q := (43299826789491895149/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14999]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14999]

theorem width_15000 : mW 15000 = 413351394094662 := by
  have hu : mW 15000 ≤ 413351394094662 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15000 ≤ 413351394094661 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15000 : RowArithmetic 15000 (1095776990255317042327/1000000000000000000000000) (59870197915238053651269/100000000000000000000000) (3056657177138169/500000000000000000000000) where
  r0 := (4252586359/7812500000000000)
  k0 := (1743975276188513/500000000000000000)
  k6 := (11180339887498949/1000000000000000000)
  q := (173205080756887729353/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15000]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15000]

theorem width_15001 : mW 15001 = 413447850790940 := by
  have hu : mW 15001 ≤ 413447850790940 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15001 ≤ 413447850790939 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15001 : RowArithmetic 15001 (1095752033059605327229/1000000000000000000000000) (59869206254642070386769/100000000000000000000000) (611225573580833/100000000000000000000000) where
  r0 := (544276625383/1000000000000000000)
  k0 := (871944041256019/250000000000000000)
  k6 := (2794991807033891/250000000000000000)
  q := (86605427081678894057/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15001]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15001]

theorem width_15002 : mW 15002 = 413544323563602 := by
  have hu : mW 15002 ≤ 413544323563602 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15002 ≤ 413544323563601 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15002 : RowArithmetic 15002 (1095727081423815081033/1000000000000000000000000) (299341073621997848697507/500000000000000000000000) (6111197373599593/1000000000000000000000000) where
  r0 := (544222205883/1000000000000000000)
  k0 := (1743800899005177/500000000000000000)
  k6 := (1397449325754221/125000000000000000)
  q := (173216627377397000283/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15002]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15002]

theorem width_15003 : mW 15003 = 413640812414256 := by
  have hu : mW 15003 ≤ 413640812414256 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15003 ≤ 413640812414255 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15003 : RowArithmetic 15003 (1095702135346324461113/1000000000000000000000000) (119734446648966324609711/200000000000000000000000) (3055069633785237/500000000000000000000000) where
  r0 := (544167795451/1000000000000000000)
  k0 := (697485490267141/200000000000000000)
  k6 := (11179222021187351/1000000000000000000)
  q := (86611200199512303029/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15003]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15003]

theorem width_15004 : mW 15004 = 413737317344509 := by
  have hu : mW 15004 ≤ 413737317344509 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15004 ≤ 413737317344508 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15004 : RowArithmetic 15004 (1095677194825512621441/1000000000000000000000000) (74832790068581832671303/125000000000000000000000) (763635177205171/125000000000000000000000) where
  r0 := (272056697043/500000000000000000)
  k0 := (3487253124999977/1000000000000000000)
  k6 := (2794712368397527/250000000000000000)
  q := (86614086614129921217/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15004]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15004]

theorem width_15005 : mW 15005 = 413833838355968 := by
  have hu : mW 15005 ≤ 413833838355968 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15005 ≤ 413833838355967 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15005 : RowArithmetic 15005 (219130451971951864121/200000000000000000000000) (598652409155191150196207/1000000000000000000000000) (61080238237327/10000000000000000000000) where
  r0 := (68007375223/125000000000000000)
  k0 := (17435394094967/5000000000000000)
  k6 := (1117847696323583/100000000000000000)
  q := (43308486466280485799/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15005]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15005]

theorem width_15006 : mW 15006 = 413930375450242 := by
  have hu : mW 15006 ≤ 413930375450242 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15006 ≤ 413930375450241 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15006 : RowArithmetic 15006 (273906832611861034993/250000000000000000000000) (299321249532083713481153/500000000000000000000000) (1221393297152979/200000000000000000000000) where
  r0 := (544004618543/1000000000000000000)
  k0 := (3486904533312613/1000000000000000000)
  k6 := (5589052245059157/500000000000000000)
  q := (10827482394351883683/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15006]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15006]

theorem width_15007 : mW 15007 = 414026928628939 := by
  have hu : mW 15007 ≤ 414026928628939 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15007 ≤ 414026928628938 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15007 : RowArithmetic 15007 (54780120329347382839/50000000000000000000000) (74829073784413742185651/125000000000000000000000) (6105909403658427/1000000000000000000000000) where
  r0 := (271975122181/500000000000000000)
  k0 := (174336513397873/50000000000000000)
  k6 := (2794433013557839/250000000000000000)
  q := (173245490561803657009/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15007]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15007]

theorem width_15008 : mW 15008 = 414123497893665 := by
  have hu : mW 15008 ≤ 414123497893665 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15008 ≤ 414123497893664 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15008 : RowArithmetic 15008 (547788744138325916781/500000000000000000000000) (598622682788345192112259/1000000000000000000000000) (1526213144333457/250000000000000000000000) where
  r0 := (543895879239/1000000000000000000)
  k0 := (1743278011462289/500000000000000000)
  k6 := (5588679827784377/500000000000000000)
  q := (34650252524332344323/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15008]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15008]

theorem width_15009 : mW 15009 = 414220083246029 := by
  have hu : mW 15009 ≤ 414220083246029 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15009 ≤ 414220083246028 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15009 : RowArithmetic 15009 (547776287757469032367/500000000000000000000000) (74826597075374975826869/125000000000000000000000) (95371812604869/15625000000000000000000) where
  r0 := (54384152317/100000000000000000)
  k0 := (3486381798204193/1000000000000000000)
  k6 := (11176987294124307/1000000000000000000)
  q := (4331425862230588843/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15009]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15009]

theorem width_15010 : mW 15010 = 414316684687640 := by
  have hu : mW 15010 ≤ 414316684687640 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15010 ≤ 414316684687639 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15010 : RowArithmetic 15010 (34235239634380885909/31250000000000000000000) (149650717929750111646911/250000000000000000000000) (6102739691712343/1000000000000000000000000) where
  r0 := (108757435231/200000000000000000)
  k0 := (69724151875987/20000000000000000)
  k6 := (11176614969891817/1000000000000000000)
  q := (21657850770563546387/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15010]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15010]

theorem width_15011 : mW 15011 = 414413302220104 := by
  have hu : mW 15011 ≤ 414413302220104 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15011 ≤ 414413302220103 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15011 : RowArithmetic 15011 (34234461457212076861/31250000000000000000000) (59859296813607388147071/100000000000000000000000) (3050841816128317/500000000000000000000000) where
  r0 := (543732838191/1000000000000000000)
  k0 := (1743016704851739/500000000000000000)
  k6 := (11176242682865087/1000000000000000000)
  q := (34653715529507077663/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15011]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15011]

theorem width_15012 : mW 15012 = 414509935845030 := by
  have hu : mW 15012 ≤ 414509935845030 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15012 ≤ 414509935845029 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15012 : RowArithmetic 15012 (43819114820204624057/40000000000000000000000) (598583065853946959839057/1000000000000000000000000) (61006278282651/10000000000000000000000) where
  r0 := (135919627319/250000000000000000)
  k0 := (3485859245913209/1000000000000000000)
  k6 := (11175870433037919/1000000000000000000)
  q := (43318587234580954187/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15012]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15012]

theorem width_15013 : mW 15013 = 414606585564026 := by
  have hu : mW 15013 ≤ 414606585564026 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15013 ≤ 414606585564025 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15013 : RowArithmetic 15013 (43818119196862398929/40000000000000000000000) (37410822804521660597201/62500000000000000000000) (7624465349573/1250000000000000000000) where
  r0 := (543624189407/1000000000000000000)
  k0 := (3485685102421969/1000000000000000000)
  k6 := (279387455510103/25000000000000000)
  q := (21660015004611608071/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15013]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15013]

theorem width_15014 : mW 15014 = 414703251378701 := by
  have hu : mW 15014 ≤ 414703251378701 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15014 ≤ 414703251378700 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15014 : RowArithmetic 15014 (1095428094878503986509/1000000000000000000000000) (149640816297749927836721/250000000000000000000000) (3049258493178603/500000000000000000000000) where
  r0 := (67946234823/125000000000000000)
  k0 := (1742755489616401/500000000000000000)
  k6 := (1396890755619687/125000000000000000)
  q := (173285890943261736747/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15014]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15014]

theorem width_15015 : mW 15015 = 414799933290661 := by
  have hu : mW 15015 ≤ 414799933290661 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15015 ≤ 414799933290660 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15015 : RowArithmetic 15015 (1095403215374333823993/1000000000000000000000000) (598553366809633460481481/1000000000000000000000000) (6097461948282269/1000000000000000000000000) where
  r0 := (543515576803/1000000000000000000)
  k0 := (871334219083981/250000000000000000)
  k6 := (2234950781338371/200000000000000000)
  q := (173291661657449635063/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15015]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15015]

theorem width_15016 : mW 15016 = 414896631301517 := by
  have hu : mW 15016 ≤ 414896631301517 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15016 ≤ 414896631301516 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15016 : RowArithmetic 15016 (1095378341407434322893/1000000000000000000000000) (74817933715996871600037/125000000000000000000000) (6096407165354293/1000000000000000000000000) where
  r0 := (271730642031/500000000000000000)
  k0 := (871290698431991/250000000000000000)
  k6 := (698398862850063/62500000000000000)
  q := (86648716089737879047/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15016]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15016]

theorem width_15017 : mW 15017 = 414993345412875 := by
  have hu : mW 15017 ≤ 414993345412875 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15017 ≤ 414993345412874 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15017 : RowArithmetic 15017 (109535347297619286953/100000000000000000000000) (598533573945751477107273/1000000000000000000000000) (609535263749409/100000000000000000000000) where
  r0 := (13585175009/25000000000000000)
  k0 := (696997746281751/200000000000000000)
  k6 := (2793502435419691/250000000000000000)
  q := (173303202509359301223/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15017]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15017]

theorem width_15018 : mW 15018 = 415090075626345 := by
  have hu : mW 15018 ≤ 415090075626345 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15018 ≤ 415090075626344 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15018 : RowArithmetic 15018 (547664305039497947309/500000000000000000000000) (598523679462690319656617/1000000000000000000000000) (3047149182311221/500000000000000000000000) where
  r0 := (271676362847/500000000000000000)
  k0 := (1742407344685859/500000000000000000)
  k6 := (5586818857459469/500000000000000000)
  q := (43327243161779864159/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15018]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15018]

theorem width_15019 : mW 15019 = 415186821943534 := by
  have hu : mW 15019 ≤ 415186821943534 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15019 ≤ 415186821943533 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15019 : RowArithmetic 15019 (1095303752714231597659/1000000000000000000000000) (598513786278518795721849/1000000000000000000000000) (1218648869332041/200000000000000000000000) where
  r0 := (543298460063/1000000000000000000)
  k0 := (696928133523337/200000000000000000)
  k6 := (5586632862657671/500000000000000000)
  q := (6932589703711016533/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15019]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15019]

theorem width_15020 : mW 15020 = 415283584366052 := by
  have hu : mW 15020 ≤ 415283584366052 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15020 ≤ 415283584366051 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15020 : RowArithmetic 15020 (1095278900880287612441/1000000000000000000000000) (598503894392964466935701/1000000000000000000000000) (243687623341129/40000000000000000000000) where
  r0 := (543244203463/1000000000000000000)
  k0 := (696893333226773/200000000000000000)
  k6 := (349152930401931/31250000000000000)
  q := (17332051234634635709/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15020]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15020]

theorem width_15021 : mW 15021 = 415380362895506 := by
  have hu : mW 15021 ≤ 415380362895506 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15021 ≤ 415380362895505 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15021 : RowArithmetic 15021 (219050810915110668011/200000000000000000000000) (299247001902877412463907/500000000000000000000000) (304556853757371/50000000000000000000000) where
  r0 := (543189955893/1000000000000000000)
  k0 := (348429268492309/100000000000000000)
  k6 := (2234504371510421/200000000000000000)
  q := (86663140953925735267/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15021]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15021]

theorem width_15022 : mW 15022 = 415477157533505 := by
  have hu : mW 15022 ≤ 415477157533505 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15022 ≤ 415477157533504 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15022 : RowArithmetic 15022 (1095229213798418004559/1000000000000000000000000) (598484114516617491690707/1000000000000000000000000) (6090083821438711/1000000000000000000000000) where
  r0 := (67891964669/125000000000000000)
  k0 := (871029680996047/250000000000000000)
  k6 := (111721499793801/10000000000000000)
  q := (17333205127730993307/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15022]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15022]

theorem width_15023 : mW 15023 = 415573968281659 := by
  have hu : mW 15023 ≤ 415573968281659 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15023 ≤ 415573968281658 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15023 : RowArithmetic 15023 (1369005473184088803/1250000000000000000000) (119694845305056035454889/200000000000000000000000) (6089030822323033/1000000000000000000000000) where
  r0 := (135770371959/250000000000000000)
  k0 := (696788956661473/200000000000000000)
  k6 := (2234355627667919/200000000000000000)
  q := (86668910227370460459/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15023]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15023]

theorem width_15024 : mW 15024 = 415670795141575 := by
  have hu : mW 15024 ≤ 415670795141575 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15024 ≤ 415670795141574 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15024 : RowArithmetic 15024 (109517954882050365511/100000000000000000000000) (598464339831470698337497/1000000000000000000000000) (3043989038860699/500000000000000000000000) where
  r0 := (543027267343/1000000000000000000)
  k0 := (1741885431444621/500000000000000000)
  k6 := (11171406334424413/1000000000000000000)
  q := (43335897360040901777/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15024]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15024]

theorem width_15025 : mW 15025 = 415767638114862 := by
  have hu : mW 15025 ≤ 415767638114862 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15025 ≤ 415767638114861 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15025 : RowArithmetic 15025 (54757736230825343361/50000000000000000000000) (149613613608729212973099/250000000000000000000000) (3043462793777409/500000000000000000000000) where
  r0 := (542973055873/1000000000000000000)
  k0 := (870899240683213/250000000000000000)
  k6 := (1396379320953547/125000000000000000)
  q := (86674679116798580739/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15025]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15025]

theorem width_15026 : mW 15026 = 415864497203130 := by
  have hu : mW 15026 ≤ 415864497203130 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15026 ≤ 415864497203129 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15026 : RowArithmetic 15026 (1095129905933671915237/1000000000000000000000000) (299222285167673301791979/500000000000000000000000) (3042936675872161/500000000000000000000000) where
  r0 := (542918853421/1000000000000000000)
  k0 := (348342308282519/100000000000000000)
  k6 := (2792665709486327/250000000000000000)
  q := (86677563417530375339/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15026]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15026]

theorem width_15027 : mW 15027 = 415961372407986 := by
  have hu : mW 15027 ≤ 415961372407986 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15027 ≤ 415961372407985 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15027 : RowArithmetic 15027 (1095105092770391798529/1000000000000000000000000) (598434687532488005412927/1000000000000000000000000) (3042410685105507/500000000000000000000000) where
  r0 := (135716164997/250000000000000000)
  k0 := (3483249223172497/1000000000000000000)
  k6 := (5585145572684517/500000000000000000)
  q := (21670111905571692271/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15027]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15027]

theorem width_15028 : mW 15028 = 416058263731040 := by
  have hu : mW 15028 ≤ 416058263731040 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15028 ≤ 416058263731039 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15028 : RowArithmetic 15028 (219016057025011790409/200000000000000000000000) (149606201506517269041351/250000000000000000000000) (3041884821437991/500000000000000000000000) where
  r0 := (542810475569/1000000000000000000)
  k0 := (3483075383761763/1000000000000000000)
  k6 := (5584959744946691/500000000000000000)
  q := (173366663462154684221/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15028]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15028]

theorem width_15029 : mW 15029 = 416155171173902 := by
  have hu : mW 15029 ≤ 416155171173902 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15029 ≤ 416155171173901 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15029 : RowArithmetic 15029 (5475277414980332051/5000000000000000000000) (299207462907909018675837/500000000000000000000000) (6082718169660347/1000000000000000000000000) where
  r0 := (542756300163/1000000000000000000)
  k0 := (3482901564592811/1000000000000000000)
  k6 := (558477393575609/50000000000000000)
  q := (86686215743911672961/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15029]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15029]

theorem width_15030 : mW 15030 = 416252094738179 := by
  have hu : mW 15030 ≤ 416252094738179 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15030 ≤ 416252094738178 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15030 : RowArithmetic 15030 (136878835797726121007/125000000000000000000000) (598405046901463113972559/1000000000000000000000000) (1216333390097061/200000000000000000000000) where
  r0 := (542702133769/1000000000000000000)
  k0 := (435340970708183/125000000000000000)
  k6 := (5584588145109629/500000000000000000)
  q := (173378199321598677169/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15030]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15030]

theorem width_15031 : mW 15031 = 416349034425480 := by
  have hu : mW 15031 ≤ 416349034425480 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15031 ≤ 416349034425479 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15031 : RowArithmetic 15031 (547502947640340621873/500000000000000000000000) (598395169282732645457419/1000000000000000000000000) (1520153996318013/250000000000000000000000) where
  r0 := (542647976383/1000000000000000000)
  k0 := (696510797393983/200000000000000000)
  k6 := (5584402373004223/500000000000000000)
  q := (6935358678539993147/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15031]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15031]

theorem width_15032 : mW 15032 = 416445990237416 := by
  have hu : mW 15032 ≤ 416445990237416 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15032 ≤ 416445990237415 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15032 : RowArithmetic 15032 (1094981109691077679691/1000000000000000000000000) (11967705859187100937513/20000000000000000000000) (3039782636970893/500000000000000000000000) where
  r0 := (108518765601/200000000000000000)
  k0 := (696476045701839/200000000000000000)
  k6 := (5584216619436789/500000000000000000)
  q := (86694867206772973983/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15032]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15032]

theorem width_15033 : mW 15033 = 416542962175595 := by
  have hu : mW 15033 ≤ 416542962175595 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15033 ≤ 416542962175594 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15033 : RowArithmetic 15033 (34217385300356077417/31250000000000000000000) (299187708965529402467339/500000000000000000000000) (303925740820789/50000000000000000000000) where
  r0 := (542539688631/1000000000000000000)
  k0 := (696441298054699/200000000000000000)
  k6 := (1396007721101061/125000000000000000)
  q := (86697750835878089693/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15033]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15033]

theorem width_15034 : mW 15034 = 416639950241626 := by
  have hu : mW 15034 ≤ 416639950241626 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15034 ≤ 416639950241625 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15034 : RowArithmetic 15034 (547465777520014024213/500000000000000000000000) (299182772098786237366799/500000000000000000000000) (6077464612615321/1000000000000000000000000) where
  r0 := (27124277913/50000000000000000)
  k0 := (1741016386131317/500000000000000000)
  k6 := (2791922583951753/250000000000000000)
  q := (86700634369074832047/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15034]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15034]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 14960 then ⟨(274194963977140145179/250000000000000000000000), (599099715443160393394491/1000000000000000000000000), (6155870143670719/1000000000000000000000000)⟩ else
  if n = 14961 then ⟨(1096754674979481478061/1000000000000000000000000), (599089746470321769917097/1000000000000000000000000), (1230960241834837/200000000000000000000000)⟩ else
  if n = 14962 then ⟨(548364749837836052467/500000000000000000000000), (299539889406019013107899/500000000000000000000000), (1538433133536911/250000000000000000000000)⟩ else
  if n = 14963 then ⟨(1096704329995488172493/1000000000000000000000000), (599069812468032070243613/1000000000000000000000000), (6152664118510269/1000000000000000000000000)⟩ else
  if n = 14964 then ⟨(274169791484321104333/250000000000000000000000), (599059847438026889475463/1000000000000000000000000), (3075797981090601/500000000000000000000000)⟩ else
  if n = 14965 then ⟨(1096654007499417383599/1000000000000000000000000), (299524941860872836740831/500000000000000000000000), (3075264032539831/500000000000000000000000)⟩ else
  if n = 14966 then ⟨(274157213670060759757/250000000000000000000000), (299519960659455751289449/500000000000000000000000), (1229892085424971/200000000000000000000000)⟩ else
  if n = 14967 then ⟨(109660370747811836391/100000000000000000000000), (299514980114623870064489/500000000000000000000000), (6148393048236033/1000000000000000000000000)⟩ else
  if n = 14968 then ⟨(1096578565891401746611/1000000000000000000000000), (599020000452477654983469/1000000000000000000000000), (614732592833251/100000000000000000000000)⟩ else
  if n = 14969 then ⟨(43862137196738039983/40000000000000000000000), (299505020994162363415943/500000000000000000000000), (6146259067333587/1000000000000000000000000)⟩ else
  if n = 14970 then ⟨(1096528299557625342729/1000000000000000000000000), (599000084836512417509571/1000000000000000000000000), (192037264536207/31250000000000000000000)⟩ else
  if n = 14971 then ⟨(1096503174807283817149/1000000000000000000000000), (598990128996764337633849/1000000000000000000000000), (6144126121726987/1000000000000000000000000)⟩ else
  if n = 14972 then ⟨(274119513916446816537/250000000000000000000000), (59898017446880410514409/100000000000000000000000), (6143060036958113/1000000000000000000000000)⟩ else
  if n = 14973 then ⟨(109645294213149556197/100000000000000000000000), (149742555313088879759737/250000000000000000000000), (1228398842154283/200000000000000000000000)⟩ else
  if n = 14974 then ⟨(548213917101385189097/500000000000000000000000), (598960269347142378395489/1000000000000000000000000), (307046432154319/50000000000000000000000)⟩ else
  if n = 14975 then ⟨(1096402731877973605103/1000000000000000000000000), (598950318752888565901061/1000000000000000000000000), (383741458363907/62500000000000000000000)⟩ else
  if n = 14976 then ⟨(109637763515546774551/100000000000000000000000), (119788073893863627953693/200000000000000000000000), (3069399141449673/500000000000000000000000)⟩ else
  if n = 14977 then ⟨(34261017001050484977/31250000000000000000000), (598930421496155076762763/1000000000000000000000000), (3068866745118217/500000000000000000000000)⟩ else
  if n = 14978 then ⟨(548163729255390524429/500000000000000000000000), (299460237416561769670961/500000000000000000000000), (6136668955753391/1000000000000000000000000)⟩ else
  if n = 14979 then ⟨(548151189292664139013/500000000000000000000000), (299455264739973881669817/500000000000000000000000), (6135604679369829/1000000000000000000000000)⟩ else
  if n = 14980 then ⟨(1096277304255622157207/1000000000000000000000000), (598900585436352065612069/1000000000000000000000000), (6134540661005409/1000000000000000000000000)⟩ else
  if n = 14981 then ⟨(1096252235520027853303/1000000000000000000000000), (299445321351030405664093/500000000000000000000000), (6133476900579811/1000000000000000000000000)⟩ else
  if n = 14982 then ⟨(548113586188455769509/500000000000000000000000), (9357510957449976142869/15625000000000000000000), (1226482679602551/200000000000000000000000)⟩ else
  if n = 14983 then ⟨(1096202114824639603239/1000000000000000000000000), (598870761160289545440587/1000000000000000000000000), (383209384576499/62500000000000000000000)⟩ else
  if n = 14984 then ⟨(548088531430789916943/500000000000000000000000), (149715205588064683697097/250000000000000000000000), (383142947883331/62500000000000000000000)⟩ else
  if n = 14985 then ⟨(274038004121524763061/250000000000000000000000), (598850884852430650091021/1000000000000000000000000), (3064612218330233/500000000000000000000000)⟩ else
  if n = 14986 then ⟨(219225395139313332023/200000000000000000000000), (37427559291283132660631/62500000000000000000000), (1532040491181343/250000000000000000000000)⟩ else
  if n = 14987 then ⟨(1096101940491350699021/1000000000000000000000000), (598831013776282006893349/1000000000000000000000000), (6127099750247849/1000000000000000000000000)⟩ else
  if n = 14988 then ⟨(137009613858602674421/125000000000000000000000), (598821080199411219126043/1000000000000000000000000), (3063018896573911/500000000000000000000000)⟩ else
  if n = 14989 then ⟨(27401297170683710089/25000000000000000000000), (9356424186400668481509/15625000000000000000000), (1224995218669041/200000000000000000000000)⟩ else
  if n = 14990 then ⟨(548013434182651387021/500000000000000000000000), (23952048678668073503129/40000000000000000000000), (612391465075997/100000000000000000000000)⟩ else
  if n = 14991 then ⟨(274000463870263844813/250000000000000000000000), (119758257462062701878167/200000000000000000000000), (6122853465312093/1000000000000000000000000)⟩ else
  if n = 14992 then ⟨(1095976848172978486471/1000000000000000000000000), (299390679480101535704659/500000000000000000000000), (612179253692161/100000000000000000000000)⟩ else
  if n = 14993 then ⟨(1095951846439444577751/1000000000000000000000000), (299385715958047934300489/500000000000000000000000), (1530182966377143/250000000000000000000000)⟩ else
  if n = 14994 then ⟨(1095926850278826350379/1000000000000000000000000), (598761506177717300042961/1000000000000000000000000), (6119671450993049/1000000000000000000000000)⟩ else
  if n = 14995 then ⟨(34246933115296809209/31250000000000000000000), (299375790872396432400823/500000000000000000000000), (6118611293295169/1000000000000000000000000)⟩ else
  if n = 14996 then ⟨(1095876874669833123067/1000000000000000000000000), (299370829308524067622241/500000000000000000000000), (764693924041883/125000000000000000000000)⟩ else
  if n = 14997 then ⟨(109585189521820694761/100000000000000000000000), (598731736794208782034597/1000000000000000000000000), (6116491748032909/1000000000000000000000000)⟩ else
  if n = 14998 then ⟨(1095826921332994887077/1000000000000000000000000), (598721816276000490247507/1000000000000000000000000), (6115432360308913/1000000000000000000000000)⟩ else
  if n = 14999 then ⟨(27395048825314316869/25000000000000000000000), (598711897062149102210131/1000000000000000000000000), (6114373229083299/1000000000000000000000000)⟩ else
  if n = 15000 then ⟨(1095776990255317042327/1000000000000000000000000), (59870197915238053651269/100000000000000000000000), (3056657177138169/500000000000000000000000)⟩ else
  if n = 15001 then ⟨(1095752033059605327229/1000000000000000000000000), (59869206254642070386769/100000000000000000000000), (611225573580833/100000000000000000000000)⟩ else
  if n = 15002 then ⟨(1095727081423815081033/1000000000000000000000000), (299341073621997848697507/500000000000000000000000), (6111197373599593/1000000000000000000000000)⟩ else
  if n = 15003 then ⟨(1095702135346324461113/1000000000000000000000000), (119734446648966324609711/200000000000000000000000), (3055069633785237/500000000000000000000000)⟩ else
  if n = 15004 then ⟨(1095677194825512621441/1000000000000000000000000), (74832790068581832671303/125000000000000000000000), (763635177205171/125000000000000000000000)⟩ else
  if n = 15005 then ⟨(219130451971951864121/200000000000000000000000), (598652409155191150196207/1000000000000000000000000), (61080238237327/10000000000000000000000)⟩ else
  if n = 15006 then ⟨(273906832611861034993/250000000000000000000000), (299321249532083713481153/500000000000000000000000), (1221393297152979/200000000000000000000000)⟩ else
  if n = 15007 then ⟨(54780120329347382839/50000000000000000000000), (74829073784413742185651/125000000000000000000000), (6105909403658427/1000000000000000000000000)⟩ else
  if n = 15008 then ⟨(547788744138325916781/500000000000000000000000), (598622682788345192112259/1000000000000000000000000), (1526213144333457/250000000000000000000000)⟩ else
  if n = 15009 then ⟨(547776287757469032367/500000000000000000000000), (74826597075374975826869/125000000000000000000000), (95371812604869/15625000000000000000000)⟩ else
  if n = 15010 then ⟨(34235239634380885909/31250000000000000000000), (149650717929750111646911/250000000000000000000000), (6102739691712343/1000000000000000000000000)⟩ else
  if n = 15011 then ⟨(34234461457212076861/31250000000000000000000), (59859296813607388147071/100000000000000000000000), (3050841816128317/500000000000000000000000)⟩ else
  if n = 15012 then ⟨(43819114820204624057/40000000000000000000000), (598583065853946959839057/1000000000000000000000000), (61006278282651/10000000000000000000000)⟩ else
  if n = 15013 then ⟨(43818119196862398929/40000000000000000000000), (37410822804521660597201/62500000000000000000000), (7624465349573/1250000000000000000000)⟩ else
  if n = 15014 then ⟨(1095428094878503986509/1000000000000000000000000), (149640816297749927836721/250000000000000000000000), (3049258493178603/500000000000000000000000)⟩ else
  if n = 15015 then ⟨(1095403215374333823993/1000000000000000000000000), (598553366809633460481481/1000000000000000000000000), (6097461948282269/1000000000000000000000000)⟩ else
  if n = 15016 then ⟨(1095378341407434322893/1000000000000000000000000), (74817933715996871600037/125000000000000000000000), (6096407165354293/1000000000000000000000000)⟩ else
  if n = 15017 then ⟨(109535347297619286953/100000000000000000000000), (598533573945751477107273/1000000000000000000000000), (609535263749409/100000000000000000000000)⟩ else
  if n = 15018 then ⟨(547664305039497947309/500000000000000000000000), (598523679462690319656617/1000000000000000000000000), (3047149182311221/500000000000000000000000)⟩ else
  if n = 15019 then ⟨(1095303752714231597659/1000000000000000000000000), (598513786278518795721849/1000000000000000000000000), (1218648869332041/200000000000000000000000)⟩ else
  if n = 15020 then ⟨(1095278900880287612441/1000000000000000000000000), (598503894392964466935701/1000000000000000000000000), (243687623341129/40000000000000000000000)⟩ else
  if n = 15021 then ⟨(219050810915110668011/200000000000000000000000), (299247001902877412463907/500000000000000000000000), (304556853757371/50000000000000000000000)⟩ else
  if n = 15022 then ⟨(1095229213798418004559/1000000000000000000000000), (598484114516617491690707/1000000000000000000000000), (6090083821438711/1000000000000000000000000)⟩ else
  if n = 15023 then ⟨(1369005473184088803/1250000000000000000000), (119694845305056035454889/200000000000000000000000), (6089030822323033/1000000000000000000000000)⟩ else
  if n = 15024 then ⟨(109517954882050365511/100000000000000000000000), (598464339831470698337497/1000000000000000000000000), (3043989038860699/500000000000000000000000)⟩ else
  if n = 15025 then ⟨(54757736230825343361/50000000000000000000000), (149613613608729212973099/250000000000000000000000), (3043462793777409/500000000000000000000000)⟩ else
  if n = 15026 then ⟨(1095129905933671915237/1000000000000000000000000), (299222285167673301791979/500000000000000000000000), (3042936675872161/500000000000000000000000)⟩ else
  if n = 15027 then ⟨(1095105092770391798529/1000000000000000000000000), (598434687532488005412927/1000000000000000000000000), (3042410685105507/500000000000000000000000)⟩ else
  if n = 15028 then ⟨(219016057025011790409/200000000000000000000000), (149606201506517269041351/250000000000000000000000), (3041884821437991/500000000000000000000000)⟩ else
  if n = 15029 then ⟨(5475277414980332051/5000000000000000000000), (299207462907909018675837/500000000000000000000000), (6082718169660347/1000000000000000000000000)⟩ else
  if n = 15030 then ⟨(136878835797726121007/125000000000000000000000), (598405046901463113972559/1000000000000000000000000), (1216333390097061/200000000000000000000000)⟩ else
  if n = 15031 then ⟨(547502947640340621873/500000000000000000000000), (598395169282732645457419/1000000000000000000000000), (1520153996318013/250000000000000000000000)⟩ else
  if n = 15032 then ⟨(1094981109691077679691/1000000000000000000000000), (11967705859187100937513/20000000000000000000000), (3039782636970893/500000000000000000000000)⟩ else
  if n = 15033 then ⟨(34217385300356077417/31250000000000000000000), (299187708965529402467339/500000000000000000000000), (303925740820789/50000000000000000000000)⟩ else
  ⟨(547465777520014024213/500000000000000000000000), (299182772098786237366799/500000000000000000000000), (6077464612615321/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14960 ≤ n) (hb : n ≤ 15034) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14960
  · exact row_14961
  · exact row_14962
  · exact row_14963
  · exact row_14964
  · exact row_14965
  · exact row_14966
  · exact row_14967
  · exact row_14968
  · exact row_14969
  · exact row_14970
  · exact row_14971
  · exact row_14972
  · exact row_14973
  · exact row_14974
  · exact row_14975
  · exact row_14976
  · exact row_14977
  · exact row_14978
  · exact row_14979
  · exact row_14980
  · exact row_14981
  · exact row_14982
  · exact row_14983
  · exact row_14984
  · exact row_14985
  · exact row_14986
  · exact row_14987
  · exact row_14988
  · exact row_14989
  · exact row_14990
  · exact row_14991
  · exact row_14992
  · exact row_14993
  · exact row_14994
  · exact row_14995
  · exact row_14996
  · exact row_14997
  · exact row_14998
  · exact row_14999
  · exact row_15000
  · exact row_15001
  · exact row_15002
  · exact row_15003
  · exact row_15004
  · exact row_15005
  · exact row_15006
  · exact row_15007
  · exact row_15008
  · exact row_15009
  · exact row_15010
  · exact row_15011
  · exact row_15012
  · exact row_15013
  · exact row_15014
  · exact row_15015
  · exact row_15016
  · exact row_15017
  · exact row_15018
  · exact row_15019
  · exact row_15020
  · exact row_15021
  · exact row_15022
  · exact row_15023
  · exact row_15024
  · exact row_15025
  · exact row_15026
  · exact row_15027
  · exact row_15028
  · exact row_15029
  · exact row_15030
  · exact row_15031
  · exact row_15032
  · exact row_15033
  · exact row_15034

end BstLean.Part271.R3.Rows14960
