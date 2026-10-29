import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14551–14625. -/
namespace BstLean.Part271.R3.Rows14551
open Real BstLean.Part130 BstLean.Part227

theorem width_14551 : mW 14551 = 371642131718034 := by
  have hu : mW 14551 ≤ 371642131718034 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14551 ≤ 371642131718033 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14551 : RowArithmetic 14551 (44302805377071726483/40000000000000000000000) (603290524482994945756767/1000000000000000000000000) (3307893145085011/500000000000000000000000) where
  r0 := (569719046711/1000000000000000000)
  k0 := (892090966983989/250000000000000000)
  k6 := (11351525149589887/1000000000000000000)
  q := (170593083095417441371/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14551]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14551]

theorem width_14552 : mW 14552 = 371731531704649 := by
  have hu : mW 14552 ≤ 371731531704649 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14552 ≤ 371731531704648 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14552 : RowArithmetic 14552 (110754250767290435927/100000000000000000000000) (603279993670445424197971/1000000000000000000000000) (1322920816374939/200000000000000000000000) where
  r0 := (56966032187/100000000000000000)
  k0 := (3568179955354621/1000000000000000000)
  k6 := (11351135109726883/1000000000000000000)
  q := (170598944897088973761/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14552]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14552]

theorem width_14553 : mW 14553 = 371820947051295 := by
  have hu : mW 14553 ≤ 371820947051295 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14553 ≤ 371820947051294 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14553 : RowArithmetic 14553 (553757443635063130337/500000000000000000000000) (301634732146421155448761/500000000000000000000000) (51667360694297/7812500000000000000000) where
  r0 := (569601607117/1000000000000000000)
  k0 := (3567996064889219/1000000000000000000)
  k6 := (709421569379161/62500000000000000)
  q := (17060480649735516757/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14553]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14553]

theorem width_14554 : mW 14554 = 371910377759555 := by
  have hu : mW 14554 ≤ 371910377759555 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14554 ≤ 371910377759554 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14554 : RowArithmetic 14554 (553743636608273829687/500000000000000000000000) (301629468174936542154351/500000000000000000000000) (3306120275530649/500000000000000000000000) where
  r0 := (569542902449/1000000000000000000)
  k0 := (1783906098266887/500000000000000000)
  k6 := (11350355150602059/1000000000000000000)
  q := (170610667896236781599/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14554]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14554]

theorem width_14555 : mW 14555 = 371999823831012 := by
  have hu : mW 14555 ≤ 371999823831012 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14555 ≤ 371999823831011 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14555 : RowArithmetic 14555 (1107459665510258084169/1000000000000000000000000) (603248409841225418843377/1000000000000000000000000) (6611059228353891/1000000000000000000000000) where
  r0 := (113896841573/200000000000000000)
  k0 := (3567628350288571/1000000000000000000)
  k6 := (11349965231326429/1000000000000000000)
  q := (170616529093754571081/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14555]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14555]

theorem width_14556 : mW 14556 = 372089285267250 := by
  have hu : mW 14556 ≤ 372089285267250 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14556 ≤ 372089285267249 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14556 : RowArithmetic 14556 (1107432064149347332637/1000000000000000000000000) (150809471191646736256217/250000000000000000000000) (6609878200653167/1000000000000000000000000) where
  r0 := (569425523361/1000000000000000000)
  k0 := (7134889052289/2000000000000000)
  k6 := (11349575352232783/1000000000000000000)
  q := (85311195044964643843/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14556]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14556]

theorem width_14557 : mW 14557 = 372178762069852 := by
  have hu : mW 14557 ≤ 372178762069852 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14557 ≤ 372178762069851 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14557 : RowArithmetic 14557 (1107404469131906404457/1000000000000000000000000) (301613680562822784334017/500000000000000000000000) (3304348733932277/500000000000000000000000) where
  r0 := (113873369787/200000000000000000)
  k0 := (356726072409871/100000000000000000)
  k6 := (567459275665711/50000000000000000)
  q := (170628250884781679521/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14557]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14557]

theorem width_14558 : mW 14558 = 372268254240402 := by
  have hu : mW 14558 ≤ 372268254240402 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14558 ≤ 372268254240401 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14558 : RowArithmetic 14558 (110737688045602656773/100000000000000000000000) (75402104864761143443649/125000000000000000000000) (6607517029893499/1000000000000000000000000) where
  r0 := (113861636917/200000000000000000)
  k0 := (3567076944148353/1000000000000000000)
  k6 := (11348795714563841/1000000000000000000)
  q := (85317055739166245563/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14558]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14558]

theorem width_14559 : mW 14559 = 372357761780483 := by
  have hu : mW 14559 ≤ 372357761780483 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14559 ≤ 372357761780482 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14559 : RowArithmetic 14559 (34604665566243759111/31250000000000000000000) (60320631814360568443971/100000000000000000000000) (1321267377329101/200000000000000000000000) where
  r0 := (142312382577/250000000000000000)
  k0 := (713378637257489/200000000000000000)
  k6 := (2837101488993687/250000000000000000)
  q := (85319985935301231741/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14559]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14559]

theorem width_14560 : mW 14560 = 372447284691679 := by
  have hu : mW 14560 ≤ 372447284691679 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14560 ≤ 372447284691678 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14560 : RowArithmetic 14560 (1107321722121320313083/1000000000000000000000000) (301597899400941657978127/500000000000000000000000) (412822314876631/62500000000000000000000) where
  r0 := (569190886103/1000000000000000000)
  k0 := (3566709450516267/1000000000000000000)
  k6 := (5674008118770023/500000000000000000)
  q := (21330729007701541751/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14560]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14560]

theorem width_14561 : mW 14561 = 372536822975574 := by
  have hu : mW 14561 ≤ 372536822975574 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14561 ≤ 372536822975573 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14561 : RowArithmetic 14561 (1107294152458680103749/1000000000000000000000000) (120637056178522033139479/200000000000000000000000) (6603977483940833/1000000000000000000000000) where
  r0 := (284566125983/500000000000000000)
  k0 := (35665257368257/10000000000000000)
  k6 := (11347626559252839/1000000000000000000)
  q := (2133146150642285457/12500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14561]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14561]

theorem width_14562 : mW 14562 = 372626376633752 := by
  have hu : mW 14562 ≤ 372626376633752 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14562 ≤ 372626376633751 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14562 : RowArithmetic 14562 (553633294564986934433/500000000000000000000000) (301587382207737278621097/500000000000000000000000) (1320559644859063/200000000000000000000000) where
  r0 := (113814725579/200000000000000000)
  k0 := (3566342045212889/1000000000000000000)
  k6 := (2836809230276559/250000000000000000)
  q := (85328775919967350719/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14562]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14562]

theorem width_14563 : mW 14563 = 372715945667795 := by
  have hu : mW 14563 ≤ 372715945667795 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14563 ≤ 372715945667794 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14563 : RowArithmetic 14563 (1107239032133297477799/1000000000000000000000000) (603164249370164804342371/1000000000000000000000000) (1320323851799043/200000000000000000000000) where
  r0 := (569015013887/1000000000000000000)
  k0 := (713231675134369/200000000000000000)
  k6 := (2269369464618669/200000000000000000)
  q := (8533170571364432769/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14563]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14563]

theorem width_14564 : mW 14564 = 372805530079289 := by
  have hu : mW 14564 ≤ 372805530079289 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14564 ≤ 372805530079288 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14564 : RowArithmetic 14564 (276802870366686417827/250000000000000000000000) (603153735756369454607747/1000000000000000000000000) (1650110146986543/250000000000000000000000) where
  r0 := (568956409941/1000000000000000000)
  k0 := (713194945640569/200000000000000000)
  k6 := (5673228882603639/500000000000000000)
  q := (666676839115099303/3906250000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14564]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14564]

theorem width_14565 : mW 14565 = 372895129869817 := by
  have hu : mW 14565 ≤ 372895129869817 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14565 ≤ 372895129869816 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14565 : RowArithmetic 14565 (1107183937128415319097/1000000000000000000000000) (603143223573776951251241/1000000000000000000000000) (3299631105526959/500000000000000000000000) where
  r0 := (284448908027/500000000000000000)
  k0 := (3565791102799897/1000000000000000000)
  k6 := (2269213649488229/200000000000000000)
  q := (1365401039987885757/8000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14565]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14565]

theorem width_14566 : mW 14566 = 372984745040963 := by
  have hu : mW 14566 ≤ 372984745040963 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14566 ≤ 372984745040962 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14566 : RowArithmetic 14566 (221431279823280711573/200000000000000000000000) (301566356411038034372513/500000000000000000000000) (3299042064112101/500000000000000000000000) where
  r0 := (17776226007/31250000000000000)
  k0 := (1782803749730071/500000000000000000)
  k6 := (11345678769788063/1000000000000000000)
  q := (85340494491185132809/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14566]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14566]

theorem width_14567 : mW 14567 = 373074375594311 := by
  have hu : mW 14567 ≤ 373074375594311 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14567 ≤ 373074375594310 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14567 : RowArithmetic 14567 (221425773485761651277/200000000000000000000000) (75390275437619437787349/125000000000000000000000) (6596906339362813/1000000000000000000000000) where
  r0 := (568780658447/1000000000000000000)
  k0 := (3565423918174451/1000000000000000000)
  k6 := (2269057866448229/200000000000000000)
  q := (170686847765139772061/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14567]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14567]

theorem width_14568 : mW 14568 = 373164021531445 := by
  have hu : mW 14568 ≤ 373164021531445 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14568 ≤ 373164021531444 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14568 : RowArithmetic 14568 (1107101342063728015141/1000000000000000000000000) (603111695610104062705147/1000000000000000000000000) (3297864422187789/500000000000000000000000) where
  r0 := (284361047361/500000000000000000)
  k0 := (3565240358943097/1000000000000000000)
  k6 := (11344899934793509/1000000000000000000)
  q := (17069270634681494791/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14568]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14568]

theorem width_14569 : mW 14569 = 373253682853949 := by
  have hu : mW 14569 ≤ 373253682853949 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14569 ≤ 373253682853948 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14569 : RowArithmetic 14569 (1107073823019262165963/1000000000000000000000000) (301550594574605358910513/500000000000000000000000) (164863791079209/25000000000000000000000) where
  r0 := (284331770523/500000000000000000)
  k0 := (3565056821760083/1000000000000000000)
  k6 := (453780423097531/40000000000000000)
  q := (21337320590927062321/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14569]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14569]

theorem width_14570 : mW 14570 = 373343359563408 := by
  have hu : mW 14570 ≤ 373343359563408 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14570 ≤ 373343359563407 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14570 : RowArithmetic 14570 (276761577573377576927/250000000000000000000000) (603090684117964465262691/1000000000000000000000000) (1318674947129409/200000000000000000000000) where
  r0 := (568604997417/1000000000000000000)
  k0 := (222804581663909/62500000000000000)
  k6 := (11344121260168563/1000000000000000000)
  q := (666814151980332523/3906250000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14570]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14570]

theorem width_14571 : mW 14571 = 373433051661406 := by
  have hu : mW 14571 ≤ 373433051661406 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14571 ≤ 373433051661405 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14571 : RowArithmetic 14571 (221403760776914646873/200000000000000000000000) (603080180516054415463811/1000000000000000000000000) (6592198121717571/1000000000000000000000000) where
  r0 := (71068307979/125000000000000000)
  k0 := (1782344906762241/500000000000000000)
  k6 := (2268746396595499/200000000000000000)
  q := (85355140442740764083/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14571]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14571]

theorem width_14572 : mW 14572 = 373522759149526 := by
  have hu : mW 14572 ≤ 373522759149526 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14572 ≤ 373522759149525 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14572 : RowArithmetic 14572 (221398260758110586753/200000000000000000000000) (603069678343169779618227/1000000000000000000000000) (3295510900642967/500000000000000000000000) where
  r0 := (56848794029/100000000000000000)
  k0 := (3564506342466163/1000000000000000000)
  k6 := (2268668549171639/200000000000000000)
  q := (170716138662986400151/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14572]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14572]

theorem width_14573 : mW 14573 = 373612482029354 := by
  have hu : mW 14573 ≤ 373612482029354 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14573 ≤ 373612482029353 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14573 : RowArithmetic 14573 (276740952502387683173/250000000000000000000000) (120611835519799974543439/200000000000000000000000) (6589845774258113/1000000000000000000000000) where
  r0 := (284214713393/500000000000000000)
  k0 := (891080723358829/250000000000000000)
  k6 := (11342953548803789/1000000000000000000)
  q := (2134024952993755413/12500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14573]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14573]

theorem width_14574 : mW 14574 = 373702220302473 := by
  have hu : mW 14574 ≤ 373702220302473 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14574 ≤ 373702220302472 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14574 : RowArithmetic 14574 (1106936322539670078587/1000000000000000000000000) (150762169570808517619151/250000000000000000000000) (6588670040540179/1000000000000000000000000) where
  r0 := (14209273083/25000000000000000)
  k0 := (1782069733217671/500000000000000000)
  k6 := (11342564391807403/1000000000000000000)
  q := (2134098170188053931/12500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14574]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14574]

theorem width_14575 : mW 14575 = 373791973970469 := by
  have hu : mW 14575 ≤ 373791973970469 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14575 ≤ 373791973970468 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14575 : RowArithmetic 14575 (110690884137901375823/100000000000000000000000) (603038180395561898329699/1000000000000000000000000) (6587494600038187/1000000000000000000000000) where
  r0 := (568312429889/1000000000000000000)
  k0 := (712791212292047/200000000000000000)
  k6 := (1417771909357771/125000000000000000)
  q := (170733710789638728569/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14575]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14575]

theorem width_14576 : mW 14576 = 373881743034926 := by
  have hu : mW 14576 ≤ 373881743034926 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14576 ≤ 373881743034925 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14576 : RowArithmetic 14576 (553440683262843107189/500000000000000000000000) (301513841967836437215739/500000000000000000000000) (823289931582283/125000000000000000000000) where
  r0 := (56825394649/100000000000000000)
  k0 := (356377267850399/100000000000000000)
  k6 := (11341786197961213/1000000000000000000)
  q := (8536978388165217793/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14576]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14576]

theorem width_14577 : mW 14577 = 373971527497427 := by
  have hu : mW 14577 ≤ 373971527497427 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14577 ≤ 373971527497426 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14577 : RowArithmetic 14577 (110685389797779308089/100000000000000000000000) (603017188903256712411087/1000000000000000000000000) (1646286149576649/250000000000000000000000) where
  r0 := (568195473121/1000000000000000000)
  k0 := (3563589317563733/1000000000000000000)
  k6 := (1134139716109767/100000000000000000)
  q := (42686356134015468339/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14577]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14577]

theorem width_14578 : mW 14578 = 374061327359559 := by
  have hu : mW 14578 ≤ 374061327359559 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14578 ≤ 374061327359558 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14578 : RowArithmetic 14578 (69176652233339929317/62500000000000000000000) (120601339059600632016789/200000000000000000000000) (6583970036889331/1000000000000000000000000) where
  r0 := (568137009779/1000000000000000000)
  k0 := (712681195726691/200000000000000000)
  k6 := (11341008164264673/1000000000000000000)
  q := (34150256221586390903/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14578]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14578]

theorem width_14579 : mW 14579 = 374151142622905 := by
  have hu : mW 14579 ≤ 374151142622905 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14579 ≤ 374151142622904 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14579 : RowArithmetic 14579 (1106798979790730669327/1000000000000000000000000) (75374525389950261170293/125000000000000000000000) (6582795768312729/1000000000000000000000000) where
  r0 := (568078556463/1000000000000000000)
  k0 := (1781611330856709/500000000000000000)
  k6 := (5670309603727679/500000000000000000)
  q := (683028549915741077/4000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14579]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14579]

theorem width_14580 : mW 14580 = 374240973289051 := by
  have hu : mW 14580 ≤ 374240973289051 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14580 ≤ 374240973289050 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14580 : RowArithmetic 14580 (1106771530147774912363/1000000000000000000000000) (602985712367743421651511/1000000000000000000000000) (6581621792483033/1000000000000000000000000) where
  r0 := (568020113169/1000000000000000000)
  k0 := (445379920849309/125000000000000000)
  k6 := (5670115145331431/500000000000000000)
  q := (21345374206136560491/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14580]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14580]

theorem width_14581 : mW 14581 = 374330819359581 := by
  have hu : mW 14581 ≤ 374330819359581 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14581 ≤ 374330819359580 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14581 : RowArithmetic 14581 (1106744086802679681203/1000000000000000000000000) (150743805760529309413639/250000000000000000000000) (6580448109306559/1000000000000000000000000) where
  r0 := (70995209987/125000000000000000)
  k0 := (1781428046938439/500000000000000000)
  k6 := (2834960353470081/250000000000000000)
  q := (667065818821969771/3906250000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14581]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14581]

theorem width_14582 : mW 14582 = 374420680836079 := by
  have hu : mW 14582 ≤ 374420680836079 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14582 ≤ 374420680836078 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14582 : RowArithmetic 14582 (1106716649753553785511/1000000000000000000000000) (120592947028482723427797/200000000000000000000000) (6579274718689661/1000000000000000000000000) where
  r0 := (1774697677/3125000000000000)
  k0 := (3562672842951483/1000000000000000000)
  k6 := (11339452577100883/1000000000000000000)
  q := (85387352693475630437/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14582]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14582]

theorem width_14583 : mW 14583 = 374510557720132 := by
  have hu : mW 14583 ≤ 374510557720132 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14583 ≤ 374510557720131 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14583 : RowArithmetic 14583 (1106689218998505376569/1000000000000000000000000) (602954248668322809779149/1000000000000000000000000) (6578101620538677/1000000000000000000000000) where
  r0 := (2839224217/5000000000000000)
  k0 := (712497922803709/200000000000000000)
  k6 := (11339063780317683/1000000000000000000)
  q := (42695140238673534541/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14583]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14583]

theorem width_14584 : mW 14584 = 374600450013323 := by
  have hu : mW 14584 ≤ 374600450013323 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14584 ≤ 374600450013322 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14584 : RowArithmetic 14584 (55333089726782258963/50000000000000000000000) (602943763619535189518269/1000000000000000000000000) (3288464407380027/500000000000000000000000) where
  r0 := (567786440173/1000000000000000000)
  k0 := (3562306407072047/1000000000000000000)
  k6 := (5669337511761933/500000000000000000)
  q := (42696604080418386361/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14584]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14584]

theorem width_14585 : mW 14585 = 374690357717238 := by
  have hu : mW 14585 ≤ 374690357717238 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14585 ≤ 374690357717237 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14585 : RowArithmetic 14585 (276658594090770814933/250000000000000000000000) (602933279995741080327839/1000000000000000000000000) (6575756301260223/1000000000000000000000000) where
  r0 := (141932011739/250000000000000000)
  k0 := (222632701381623/62500000000000000)
  k6 := (5669143153356289/500000000000000000)
  q := (170792271487910131373/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14585]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14585]

theorem width_14586 : mW 14586 = 374780280833462 := by
  have hu : mW 14586 ≤ 374780280833462 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14586 ≤ 374780280833461 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14586 : RowArithmetic 14586 (276651741119732717951/250000000000000000000000) (120584559559326197351911/200000000000000000000000) (6574584079945669/1000000000000000000000000) where
  r0 := (141917415937/250000000000000000)
  k0 := (890485014780141/250000000000000000)
  k6 := (11337897629876967/1000000000000000000)
  q := (170798126453424541071/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14586]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14586]

theorem width_14587 : mW 14587 = 374870219363580 := by
  have hu : mW 14587 ≤ 374870219363580 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14587 ≤ 374870219363579 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14587 : RowArithmetic 14587 (221315911776259998973/200000000000000000000000) (602912317021895585781971/1000000000000000000000000) (3286706075361459/500000000000000000000000) where
  r0 := (283805645273/500000000000000000)
  k0 := (890439229527453/250000000000000000)
  k6 := (566875449650509/50000000000000000)
  q := (170803981218237416119/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14587]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14587]

theorem width_14588 : mW 14588 = 374960173309177 := by
  have hu : mW 14588 ≤ 374960173309177 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14588 ≤ 374960173309176 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14588 : RowArithmetic 14588 (1106552159568303333519/1000000000000000000000000) (301450918835612759017679/500000000000000000000000) (6572240513498529/1000000000000000000000000) where
  r0 := (567552927347/1000000000000000000)
  k0 := (3561573799067689/1000000000000000000)
  k6 := (1417140049513171/125000000000000000)
  q := (170809835782369394561/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14588]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14588]

theorem width_14589 : mW 14589 = 375050142671838 := by
  have hu : mW 14589 ≤ 375050142671838 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14589 ≤ 375050142671837 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14589 : RowArithmetic 14589 (1106524766538054317217/1000000000000000000000000) (602891359744311533595293/1000000000000000000000000) (6571069168179101/1000000000000000000000000) where
  r0 := (567494574149/1000000000000000000)
  k0 := (356139070199131/100000000000000000)
  k6 := (11336731839155683/1000000000000000000)
  q := (21351961268230138863/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14589]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14589]

theorem width_14590 : mW 14590 = 375140127453149 := by
  have hu : mW 14590 ≤ 375140127453149 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14590 ≤ 375140127453148 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14590 : RowArithmetic 14590 (1106497379788666639641/1000000000000000000000000) (301440441620422268749033/500000000000000000000000) (6569898114671253/1000000000000000000000000) where
  r0 := (11348724619/20000000000000000)
  k0 := (712241525375557/200000000000000000)
  k6 := (5668171661077139/500000000000000000)
  q := (170821544308673196119/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14590]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14590]

theorem width_14591 : mW 14591 = 375230127654695 := by
  have hu : mW 14591 ≤ 375230127654695 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14591 ≤ 375230127654694 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14591 : RowArithmetic 14591 (55323499965912758971/50000000000000000000000) (150717602040128870578477/250000000000000000000000) (3284363676440829/500000000000000000000000) where
  r0 := (567377897747/1000000000000000000)
  k0 := (6955126120549/1953125000000000)
  k6 := (11335954845094309/1000000000000000000)
  q := (170827398270886277641/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14591]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14591]

theorem width_14592 : mW 14592 = 375320143278061 := by
  have hu : mW 14592 ≤ 375320143278061 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14592 ≤ 375320143278060 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14592 : RowArithmetic 14592 (1106442625124935538957/1000000000000000000000000) (3014299672515077319553/5000000000000000000000) (6567556882717027/1000000000000000000000000) where
  r0 := (283659787269/500000000000000000)
  k0 := (445105192814791/125000000000000000)
  k6 := (11335566407968933/1000000000000000000)
  q := (170833252032500979373/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14592]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14592]

theorem width_14593 : mW 14593 = 375410174324833 := by
  have hu : mW 14593 ≤ 375410174324833 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14593 ≤ 375410174324832 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14593 : RowArithmetic 14593 (221283051441364716871/200000000000000000000000) (120569892453607116256949/200000000000000000000000) (6566386704084091/1000000000000000000000000) where
  r0 := (567261261321/1000000000000000000)
  k0 := (1780329266633307/500000000000000000)
  k6 := (11335178010771307/1000000000000000000)
  q := (170839105593537921683/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14593]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14593]

theorem width_14594 : mW 14594 = 375500220796597 := by
  have hu : mW 14594 ≤ 375500220796597 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14594 ≤ 375500220796596 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14594 : RowArithmetic 14594 (221277579112407181101/200000000000000000000000) (301419495727633535342227/500000000000000000000000) (6565216816889617/1000000000000000000000000) where
  r0 := (141800739523/250000000000000000)
  k0 := (445059443244597/125000000000000000)
  k6 := (11334789653494593/1000000000000000000)
  q := (170844958954017721407/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14594]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14594]

theorem width_14595 : mW 14595 = 375590282694937 := by
  have hu : mW 14595 ≤ 375590282694937 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14595 ≤ 375590282694936 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14595 : RowArithmetic 14595 (138295067523586341803/125000000000000000000000) (301414261032200638152473/500000000000000000000000) (3282023610520223/500000000000000000000000) where
  r0 := (567144664851/1000000000000000000)
  k0 := (1780146290296099/500000000000000000)
  k6 := (708400083508247/62500000000000000)
  q := (21356351514245123981/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14595]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14595]

theorem width_14596 : mW 14596 = 375680360021439 := by
  have hu : mW 14596 ≤ 375680360021439 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14596 ≤ 375680360021438 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14596 : RowArithmetic 14596 (1106333191084906106403/1000000000000000000000000) (120563610819025934195521/200000000000000000000000) (328143895822171/50000000000000000000000) where
  r0 := (567086381593/1000000000000000000)
  k0 := (445013704645071/125000000000000000)
  k6 := (11334013058676547/1000000000000000000)
  q := (170856665073388342781/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14596]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14596]

theorem width_14597 : mW 14597 = 375770452777690 := by
  have hu : mW 14597 ≤ 375770452777690 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14597 ≤ 375770452777689 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14597 : RowArithmetic 14597 (110630584824880032047/100000000000000000000000) (602807587547143699510161/1000000000000000000000000) (3280854451502701/500000000000000000000000) where
  r0 := (283514054159/500000000000000000)
  k0 := (889981678916317/250000000000000000)
  k6 := (11333624821121543/1000000000000000000)
  q := (5339453682260011889/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14597]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14597]

theorem width_14598 : mW 14598 = 375860560965274 := by
  have hu : mW 14598 ≤ 375860560965274 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14598 ≤ 375860560965273 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14598 : RowArithmetic 14598 (553139255839246887563/500000000000000000000000) (301398561210067486681479/500000000000000000000000) (25627110080599/3906250000000000000000) where
  r0 := (283484922511/500000000000000000)
  k0 := (1779871908048561/500000000000000000)
  k6 := (11333236623460107/1000000000000000000)
  q := (42717092597694426891/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14598]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14598]

theorem width_14599 : mW 14599 = 375950684585778 := by
  have hu : mW 14599 ≤ 375950684585778 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14599 ≤ 375950684585777 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14599 : RowArithmetic 14599 (553125590686053106783/500000000000000000000000) (9418541542403050141803/15625000000000000000000) (6559371749234183/1000000000000000000000000) where
  r0 := (566911591703/1000000000000000000)
  k0 := (222472558653327/62500000000000000)
  k6 := (354151514552669/31250000000000000)
  q := (85437111374390461657/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14599]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14599]

theorem width_14600 : mW 14600 = 376040823640788 := by
  have hu : mW 14600 ≤ 376040823640788 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14600 ≤ 376040823640787 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14600 : RowArithmetic 14600 (1106223857327758559781/1000000000000000000000000) (150694049106954066945023/250000000000000000000000) (6558203608714911/1000000000000000000000000) where
  r0 := (283426674179/500000000000000000)
  k0 := (1779689041363779/500000000000000000)
  k6 := (2266492069558123/200000000000000000)
  q := (85440037453175311679/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14600]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14600]

theorem width_14601 : mW 14601 = 376130978131888 := by
  have hu : mW 14601 ≤ 376130978131888 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14601 ≤ 376130978131887 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14601 : RowArithmetic 14601 (553098269771786687771/500000000000000000000000) (60276573556188992659897/100000000000000000000000) (102453683734103/15625000000000000000000) where
  r0 := (283397557493/500000000000000000)
  k0 := (1779597624460169/500000000000000000)
  k6 := (113320722697689/10000000000000000)
  q := (170885926863507399827/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14601]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14601]

theorem width_14602 : mW 14602 = 376221148060666 := by
  have hu : mW 14602 ≤ 376221148060666 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14602 ≤ 376221148060665 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14602 : RowArithmetic 14602 (1106169228017672109817/1000000000000000000000000) (964408441785133106177/1600000000000000000000) (102435440624129/15625000000000000000000) where
  r0 := (8855263931/15625000000000000)
  k0 := (355901243702553/100000000000000000)
  k6 := (2832921057903359/250000000000000000)
  q := (170891778620271841327/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14602]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14602]

theorem width_14603 : mW 14603 = 376311333428707 := by
  have hu : mW 14603 ≤ 376311333428707 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14603 ≤ 376311333428706 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14603 : RowArithmetic 14603 (553070961374089153623/500000000000000000000000) (150686204522240780982487/250000000000000000000000) (3277350465753513/500000000000000000000000) where
  r0 := (11333573563/20000000000000000)
  k0 := (444853705880029/125000000000000000)
  k6 := (5665648116658699/500000000000000000)
  q := (8544881508833226647/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14603]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14603]

theorem width_14604 : mW 14604 = 376401534237597 := by
  have hu : mW 14604 ≤ 376401534237597 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14604 ≤ 376401534237596 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14604 : RowArithmetic 14604 (1106114623733215774251/1000000000000000000000000) (602734361481346942824457/1000000000000000000000000) (163838348839451/25000000000000000000000) where
  r0 := (566620474681/1000000000000000000)
  k0 := (3558646878958399/1000000000000000000)
  k6 := (11330908274873963/1000000000000000000)
  q := (85451740766353028111/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14604]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14604]

theorem width_14605 : mW 14605 = 376491750488922 := by
  have hu : mW 14605 ≤ 376491750488922 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14605 ≤ 376491750488921 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14605 : RowArithmetic 14605 (1106087330970909037101/1000000000000000000000000) (602723906292551792571459/1000000000000000000000000) (3276183633032239/500000000000000000000000) where
  r0 := (283281140587/500000000000000000)
  k0 := (111202004149187/31250000000000000)
  k6 := (2832630089069077/250000000000000000)
  q := (170909332688416989209/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14605]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14605]

theorem width_14606 : mW 14606 = 376581982184269 := by
  have hu : mW 14606 ≤ 376581982184269 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14606 ≤ 376581982184268 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14606 : RowArithmetic 14606 (553030022229691442111/500000000000000000000000) (301356726261135055635627/500000000000000000000000) (6551200868873537/1000000000000000000000000) where
  r0 := (141626024407/250000000000000000)
  k0 := (3558281408487221/1000000000000000000)
  k6 := (5665066238758807/500000000000000000)
  q := (170915183643817906411/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14606]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14606]

theorem width_14607 : mW 14607 = 376672229325223 := by
  have hu : mW 14607 ≤ 376672229325223 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14607 ≤ 376672229325222 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14607 : RowArithmetic 14607 (1106032764196763738217/1000000000000000000000000) (602703000170194298947939/1000000000000000000000000) (3275017380956243/500000000000000000000000) where
  r0 := (14161148101/25000000000000000)
  k0 := (1779049353046031/500000000000000000)
  k6 := (5664872319295531/500000000000000000)
  q := (85460517199464689409/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14607]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14607]

theorem width_14608 : mW 14608 = 376762491913371 := by
  have hu : mW 14608 ≤ 376762491913371 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14608 ≤ 376762491913370 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14608 : RowArithmetic 14608 (221201098036235565159/200000000000000000000000) (602692549236016830578527/1000000000000000000000000) (1637217236272149/250000000000000000000000) where
  r0 := (566387760407/1000000000000000000)
  k0 := (711583205116491/200000000000000000)
  k6 := (5664678419744917/500000000000000000)
  q := (1709268849537719739/10000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14608]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14608]

theorem width_14609 : mW 14609 = 376852769950300 := by
  have hu : mW 14609 ≤ 376852769950300 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14609 ≤ 376852769950299 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14609 : RowArithmetic 14609 (55298911120537604641/50000000000000000000000) (301341049859715195970151/500000000000000000000000) (6547703418309177/1000000000000000000000000) where
  r0 := (70791200841/125000000000000000)
  k0 := (444716670869829/125000000000000000)
  k6 := (2832242270051779/250000000000000000)
  q := (170932735308366255607/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14609]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14609]

theorem width_14610 : mW 14610 = 376943063437594 := by
  have hu : mW 14610 ≤ 376943063437594 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14610 ≤ 376943063437593 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14610 : RowArithmetic 14610 (1105950960883615573773/1000000000000000000000000) (24106866064805105943207/40000000000000000000000) (3273269090740813/500000000000000000000000) where
  r0 := (566271462999/1000000000000000000)
  k0 := (1778775365105699/500000000000000000)
  k6 := (5664290680368047/500000000000000000)
  q := (10683661591420799023/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14610]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14610]

theorem width_14611 : mW 14611 = 377033372376842 := by
  have hu : mW 14611 ≤ 377033372376842 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14611 ≤ 377033372376841 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14611 : RowArithmetic 14611 (69120231599868483579/62500000000000000000000) (602661204937801430803853/1000000000000000000000000) (6545373234513293/1000000000000000000000000) where
  r0 := (566213329219/1000000000000000000)
  k0 := (1778684057670491/500000000000000000)
  k6 := (2832048420267489/250000000000000000)
  q := (170944435416892117097/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14611]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14611]

theorem width_14612 : mW 14612 = 377123696769630 := by
  have hu : mW 14612 ≤ 377123696769630 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14612 ≤ 377123696769629 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14612 : RowArithmetic 14612 (1105896456551722140177/1000000000000000000000000) (1883283623975451962363/3125000000000000000000) (6544208577311613/1000000000000000000000000) where
  r0 := (113231041077/200000000000000000)
  k0 := (3557185522341329/1000000000000000000)
  k6 := (2831951510300473/250000000000000000)
  q := (170950285170864807189/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14612]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14612]

theorem width_14613 : mW 14613 = 377214036617543 := by
  have hu : mW 14613 ≤ 377214036617543 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14613 ≤ 377214036617542 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14613 : RowArithmetic 14613 (221173842748645102491/200000000000000000000000) (602640315822850151458823/1000000000000000000000000) (81788052622301/12500000000000000000000) where
  r0 := (113219418299/200000000000000000)
  k0 := (3557002951209523/1000000000000000000)
  k6 := (2831854610281273/250000000000000000)
  q := (85478067362335702261/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14613]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14613]

theorem width_14614 : mW 14614 = 377304391922168 := by
  have hu : mW 14614 ≤ 377304391922168 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14614 ≤ 377304391922167 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14614 : RowArithmetic 14614 (1105841977170536388201/1000000000000000000000000) (75328734173701395256503/125000000000000000000000) (6541880131838187/1000000000000000000000000) where
  r0 := (283019493773/500000000000000000)
  k0 := (711364080387901/200000000000000000)
  k6 := (11327030880832749/1000000000000000000)
  q := (8548099203916622773/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14614]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14614]

theorem width_14615 : mW 14615 = 377394762685093 := by
  have hu : mW 14615 ≤ 377394762685093 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14615 ≤ 377394762685092 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14615 : RowArithmetic 14615 (1105814746831785562841/1000000000000000000000000) (602619432372120753626241/1000000000000000000000000) (6540716343381447/1000000000000000000000000) where
  r0 := (17686902923/31250000000000000)
  k0 := (3556637874528359/1000000000000000000)
  k6 := (11326643360318059/1000000000000000000)
  q := (3419356664637370057/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14615]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14615]

theorem width_14616 : mW 14616 = 377485148907904 := by
  have hu : mW 14616 ≤ 377485148907904 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14616 ≤ 377485148907903 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14616 : RowArithmetic 14616 (552893761362552730109/500000000000000000000000) (301304496385036106048881/500000000000000000000000) (6539552844321447/1000000000000000000000000) where
  r0 := (282961404731/500000000000000000)
  k0 := (3556455368970023/1000000000000000000)
  k6 := (1415781984946777/125000000000000000)
  q := (170973682185300086027/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14616]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14616]

theorem width_14617 : mW 14617 = 377575550592187 := by
  have hu : mW 14617 ≤ 377575550592187 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14617 ≤ 377575550592186 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14617 : RowArithmetic 14617 (552880152424314609881/500000000000000000000000) (150649638645789740431941/250000000000000000000000) (6538389634565809/1000000000000000000000000) where
  r0 := (565864735323/1000000000000000000)
  k0 := (44453411065809/12500000000000000)
  k6 := (11325868438594419/1000000000000000000)
  q := (42744882734661935203/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14617]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14617]

theorem width_14618 : mW 14618 = 377665967739530 := by
  have hu : mW 14618 ≤ 377665967739530 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14618 ≤ 377665967739529 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14618 : RowArithmetic 14618 (1105733093200489785817/1000000000000000000000000) (150647029452768570871021/250000000000000000000000) (1634306678505539/250000000000000000000000) where
  r0 := (113161334223/200000000000000000)
  k0 := (3556090423403243/1000000000000000000)
  k6 := (2831370259342967/250000000000000000)
  q := (85492689745965999757/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14618]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14618]

theorem width_14619 : mW 14619 = 377756400351519 := by
  have hu : mW 14619 ≤ 377756400351519 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14619 ≤ 377756400351518 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14619 : RowArithmetic 14619 (552852943889410864501/500000000000000000000000) (602577682453511791796281/1000000000000000000000000) (3268032041299093/500000000000000000000000) where
  r0 := (565748616837/1000000000000000000)
  k0 := (888976995846453/250000000000000000)
  k6 := (5662546837949881/500000000000000000)
  q := (17099122784517339093/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14619]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14619]

theorem width_14620 : mW 14620 = 377846848429741 := by
  have hu : mW 14620 ≤ 377846848429741 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14620 ≤ 377846848429740 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14620 : RowArithmetic 14620 (1105678688581759879657/1000000000000000000000000) (301283624255082578335539/500000000000000000000000) (3267450870100807/500000000000000000000000) where
  r0 := (282845286243/500000000000000000)
  k0 := (1777862782603181/500000000000000000)
  k6 := (5662353177085653/500000000000000000)
  q := (42749268999598110087/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14620]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14620]

theorem width_14621 : mW 14621 = 377937311975783 := by
  have hu : mW 14621 ≤ 377937311975783 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14621 ≤ 377937311975782 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14621 : RowArithmetic 14621 (138206436950929972877/125000000000000000000000) (602556815980727968370429/1000000000000000000000000) (6533739686740193/1000000000000000000000000) where
  r0 := (565632538059/1000000000000000000)
  k0 := (142221726754353/40000000000000000)
  k6 := (5662159536089851/500000000000000000)
  q := (34200584790321933909/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14621]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14621]

theorem width_14622 : mW 14622 = 378027790991232 := by
  have hu : mW 14622 ≤ 378027790991232 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14622 ≤ 378027790991231 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14622 : RowArithmetic 14622 (34550759651687428089/31250000000000000000000) (150636596216223532449541/250000000000000000000000) (408286120132607/62500000000000000000000) where
  r0 := (113114902711/200000000000000000)
  k0 := (3555360794343417/1000000000000000000)
  k6 := (11323931829918157/1000000000000000000)
  q := (171008771704845596789/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14622]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14622]

theorem width_14623 : mW 14623 = 378118285477676 := by
  have hu : mW 14623 ≤ 378118285477676 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14623 ≤ 378118285477675 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14623 : RowArithmetic 14623 (552798564159785073427/500000000000000000000000) (18829248598823670420723/31250000000000000000000) (6531416446253981/1000000000000000000000000) where
  r0 := (565516498971/1000000000000000000)
  k0 := (3555178441654069/1000000000000000000)
  k6 := (5661772313689939/500000000000000000)
  q := (4275365481453018421/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14623]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14623]

theorem width_14624 : mW 14624 = 378208795436700 := by
  have hu : mW 14624 ≤ 378208795436700 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14624 ≤ 378208795436699 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14624 : RowArithmetic 14624 (276392488500573930873/250000000000000000000000) (150631381718203006533221/250000000000000000000000) (6530255259044897/1000000000000000000000000) where
  r0 := (17670577947/31250000000000000)
  k0 := (3554996110784709/1000000000000000000)
  k6 := (452926298582323/40000000000000000)
  q := (21377558326431950119/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14624]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14624]

theorem width_14625 : mW 14625 = 378299320869894 := by
  have hu : mW 14625 ≤ 378299320869894 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14625 ≤ 378299320869893 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14625 : RowArithmetic 14625 (276385696475077866953/250000000000000000000000) (75314387499493973165751/125000000000000000000000) (6529094360402309/1000000000000000000000000) where
  r0 := (17668765611/31250000000000000)
  k0 := (1777406900866203/500000000000000000)
  k6 := (5661385170722979/500000000000000000)
  q := (171026313764870696871/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14625]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14625]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 14551 then ⟨(44302805377071726483/40000000000000000000000), (603290524482994945756767/1000000000000000000000000), (3307893145085011/500000000000000000000000)⟩ else
  if n = 14552 then ⟨(110754250767290435927/100000000000000000000000), (603279993670445424197971/1000000000000000000000000), (1322920816374939/200000000000000000000000)⟩ else
  if n = 14553 then ⟨(553757443635063130337/500000000000000000000000), (301634732146421155448761/500000000000000000000000), (51667360694297/7812500000000000000000)⟩ else
  if n = 14554 then ⟨(553743636608273829687/500000000000000000000000), (301629468174936542154351/500000000000000000000000), (3306120275530649/500000000000000000000000)⟩ else
  if n = 14555 then ⟨(1107459665510258084169/1000000000000000000000000), (603248409841225418843377/1000000000000000000000000), (6611059228353891/1000000000000000000000000)⟩ else
  if n = 14556 then ⟨(1107432064149347332637/1000000000000000000000000), (150809471191646736256217/250000000000000000000000), (6609878200653167/1000000000000000000000000)⟩ else
  if n = 14557 then ⟨(1107404469131906404457/1000000000000000000000000), (301613680562822784334017/500000000000000000000000), (3304348733932277/500000000000000000000000)⟩ else
  if n = 14558 then ⟨(110737688045602656773/100000000000000000000000), (75402104864761143443649/125000000000000000000000), (6607517029893499/1000000000000000000000000)⟩ else
  if n = 14559 then ⟨(34604665566243759111/31250000000000000000000), (60320631814360568443971/100000000000000000000000), (1321267377329101/200000000000000000000000)⟩ else
  if n = 14560 then ⟨(1107321722121320313083/1000000000000000000000000), (301597899400941657978127/500000000000000000000000), (412822314876631/62500000000000000000000)⟩ else
  if n = 14561 then ⟨(1107294152458680103749/1000000000000000000000000), (120637056178522033139479/200000000000000000000000), (6603977483940833/1000000000000000000000000)⟩ else
  if n = 14562 then ⟨(553633294564986934433/500000000000000000000000), (301587382207737278621097/500000000000000000000000), (1320559644859063/200000000000000000000000)⟩ else
  if n = 14563 then ⟨(1107239032133297477799/1000000000000000000000000), (603164249370164804342371/1000000000000000000000000), (1320323851799043/200000000000000000000000)⟩ else
  if n = 14564 then ⟨(276802870366686417827/250000000000000000000000), (603153735756369454607747/1000000000000000000000000), (1650110146986543/250000000000000000000000)⟩ else
  if n = 14565 then ⟨(1107183937128415319097/1000000000000000000000000), (603143223573776951251241/1000000000000000000000000), (3299631105526959/500000000000000000000000)⟩ else
  if n = 14566 then ⟨(221431279823280711573/200000000000000000000000), (301566356411038034372513/500000000000000000000000), (3299042064112101/500000000000000000000000)⟩ else
  if n = 14567 then ⟨(221425773485761651277/200000000000000000000000), (75390275437619437787349/125000000000000000000000), (6596906339362813/1000000000000000000000000)⟩ else
  if n = 14568 then ⟨(1107101342063728015141/1000000000000000000000000), (603111695610104062705147/1000000000000000000000000), (3297864422187789/500000000000000000000000)⟩ else
  if n = 14569 then ⟨(1107073823019262165963/1000000000000000000000000), (301550594574605358910513/500000000000000000000000), (164863791079209/25000000000000000000000)⟩ else
  if n = 14570 then ⟨(276761577573377576927/250000000000000000000000), (603090684117964465262691/1000000000000000000000000), (1318674947129409/200000000000000000000000)⟩ else
  if n = 14571 then ⟨(221403760776914646873/200000000000000000000000), (603080180516054415463811/1000000000000000000000000), (6592198121717571/1000000000000000000000000)⟩ else
  if n = 14572 then ⟨(221398260758110586753/200000000000000000000000), (603069678343169779618227/1000000000000000000000000), (3295510900642967/500000000000000000000000)⟩ else
  if n = 14573 then ⟨(276740952502387683173/250000000000000000000000), (120611835519799974543439/200000000000000000000000), (6589845774258113/1000000000000000000000000)⟩ else
  if n = 14574 then ⟨(1106936322539670078587/1000000000000000000000000), (150762169570808517619151/250000000000000000000000), (6588670040540179/1000000000000000000000000)⟩ else
  if n = 14575 then ⟨(110690884137901375823/100000000000000000000000), (603038180395561898329699/1000000000000000000000000), (6587494600038187/1000000000000000000000000)⟩ else
  if n = 14576 then ⟨(553440683262843107189/500000000000000000000000), (301513841967836437215739/500000000000000000000000), (823289931582283/125000000000000000000000)⟩ else
  if n = 14577 then ⟨(110685389797779308089/100000000000000000000000), (603017188903256712411087/1000000000000000000000000), (1646286149576649/250000000000000000000000)⟩ else
  if n = 14578 then ⟨(69176652233339929317/62500000000000000000000), (120601339059600632016789/200000000000000000000000), (6583970036889331/1000000000000000000000000)⟩ else
  if n = 14579 then ⟨(1106798979790730669327/1000000000000000000000000), (75374525389950261170293/125000000000000000000000), (6582795768312729/1000000000000000000000000)⟩ else
  if n = 14580 then ⟨(1106771530147774912363/1000000000000000000000000), (602985712367743421651511/1000000000000000000000000), (6581621792483033/1000000000000000000000000)⟩ else
  if n = 14581 then ⟨(1106744086802679681203/1000000000000000000000000), (150743805760529309413639/250000000000000000000000), (6580448109306559/1000000000000000000000000)⟩ else
  if n = 14582 then ⟨(1106716649753553785511/1000000000000000000000000), (120592947028482723427797/200000000000000000000000), (6579274718689661/1000000000000000000000000)⟩ else
  if n = 14583 then ⟨(1106689218998505376569/1000000000000000000000000), (602954248668322809779149/1000000000000000000000000), (6578101620538677/1000000000000000000000000)⟩ else
  if n = 14584 then ⟨(55333089726782258963/50000000000000000000000), (602943763619535189518269/1000000000000000000000000), (3288464407380027/500000000000000000000000)⟩ else
  if n = 14585 then ⟨(276658594090770814933/250000000000000000000000), (602933279995741080327839/1000000000000000000000000), (6575756301260223/1000000000000000000000000)⟩ else
  if n = 14586 then ⟨(276651741119732717951/250000000000000000000000), (120584559559326197351911/200000000000000000000000), (6574584079945669/1000000000000000000000000)⟩ else
  if n = 14587 then ⟨(221315911776259998973/200000000000000000000000), (602912317021895585781971/1000000000000000000000000), (3286706075361459/500000000000000000000000)⟩ else
  if n = 14588 then ⟨(1106552159568303333519/1000000000000000000000000), (301450918835612759017679/500000000000000000000000), (6572240513498529/1000000000000000000000000)⟩ else
  if n = 14589 then ⟨(1106524766538054317217/1000000000000000000000000), (602891359744311533595293/1000000000000000000000000), (6571069168179101/1000000000000000000000000)⟩ else
  if n = 14590 then ⟨(1106497379788666639641/1000000000000000000000000), (301440441620422268749033/500000000000000000000000), (6569898114671253/1000000000000000000000000)⟩ else
  if n = 14591 then ⟨(55323499965912758971/50000000000000000000000), (150717602040128870578477/250000000000000000000000), (3284363676440829/500000000000000000000000)⟩ else
  if n = 14592 then ⟨(1106442625124935538957/1000000000000000000000000), (3014299672515077319553/5000000000000000000000), (6567556882717027/1000000000000000000000000)⟩ else
  if n = 14593 then ⟨(221283051441364716871/200000000000000000000000), (120569892453607116256949/200000000000000000000000), (6566386704084091/1000000000000000000000000)⟩ else
  if n = 14594 then ⟨(221277579112407181101/200000000000000000000000), (301419495727633535342227/500000000000000000000000), (6565216816889617/1000000000000000000000000)⟩ else
  if n = 14595 then ⟨(138295067523586341803/125000000000000000000000), (301414261032200638152473/500000000000000000000000), (3282023610520223/500000000000000000000000)⟩ else
  if n = 14596 then ⟨(1106333191084906106403/1000000000000000000000000), (120563610819025934195521/200000000000000000000000), (328143895822171/50000000000000000000000)⟩ else
  if n = 14597 then ⟨(110630584824880032047/100000000000000000000000), (602807587547143699510161/1000000000000000000000000), (3280854451502701/500000000000000000000000)⟩ else
  if n = 14598 then ⟨(553139255839246887563/500000000000000000000000), (301398561210067486681479/500000000000000000000000), (25627110080599/3906250000000000000000)⟩ else
  if n = 14599 then ⟨(553125590686053106783/500000000000000000000000), (9418541542403050141803/15625000000000000000000), (6559371749234183/1000000000000000000000000)⟩ else
  if n = 14600 then ⟨(1106223857327758559781/1000000000000000000000000), (150694049106954066945023/250000000000000000000000), (6558203608714911/1000000000000000000000000)⟩ else
  if n = 14601 then ⟨(553098269771786687771/500000000000000000000000), (60276573556188992659897/100000000000000000000000), (102453683734103/15625000000000000000000)⟩ else
  if n = 14602 then ⟨(1106169228017672109817/1000000000000000000000000), (964408441785133106177/1600000000000000000000), (102435440624129/15625000000000000000000)⟩ else
  if n = 14603 then ⟨(553070961374089153623/500000000000000000000000), (150686204522240780982487/250000000000000000000000), (3277350465753513/500000000000000000000000)⟩ else
  if n = 14604 then ⟨(1106114623733215774251/1000000000000000000000000), (602734361481346942824457/1000000000000000000000000), (163838348839451/25000000000000000000000)⟩ else
  if n = 14605 then ⟨(1106087330970909037101/1000000000000000000000000), (602723906292551792571459/1000000000000000000000000), (3276183633032239/500000000000000000000000)⟩ else
  if n = 14606 then ⟨(553030022229691442111/500000000000000000000000), (301356726261135055635627/500000000000000000000000), (6551200868873537/1000000000000000000000000)⟩ else
  if n = 14607 then ⟨(1106032764196763738217/1000000000000000000000000), (602703000170194298947939/1000000000000000000000000), (3275017380956243/500000000000000000000000)⟩ else
  if n = 14608 then ⟨(221201098036235565159/200000000000000000000000), (602692549236016830578527/1000000000000000000000000), (1637217236272149/250000000000000000000000)⟩ else
  if n = 14609 then ⟨(55298911120537604641/50000000000000000000000), (301341049859715195970151/500000000000000000000000), (6547703418309177/1000000000000000000000000)⟩ else
  if n = 14610 then ⟨(1105950960883615573773/1000000000000000000000000), (24106866064805105943207/40000000000000000000000), (3273269090740813/500000000000000000000000)⟩ else
  if n = 14611 then ⟨(69120231599868483579/62500000000000000000000), (602661204937801430803853/1000000000000000000000000), (6545373234513293/1000000000000000000000000)⟩ else
  if n = 14612 then ⟨(1105896456551722140177/1000000000000000000000000), (1883283623975451962363/3125000000000000000000), (6544208577311613/1000000000000000000000000)⟩ else
  if n = 14613 then ⟨(221173842748645102491/200000000000000000000000), (602640315822850151458823/1000000000000000000000000), (81788052622301/12500000000000000000000)⟩ else
  if n = 14614 then ⟨(1105841977170536388201/1000000000000000000000000), (75328734173701395256503/125000000000000000000000), (6541880131838187/1000000000000000000000000)⟩ else
  if n = 14615 then ⟨(1105814746831785562841/1000000000000000000000000), (602619432372120753626241/1000000000000000000000000), (6540716343381447/1000000000000000000000000)⟩ else
  if n = 14616 then ⟨(552893761362552730109/500000000000000000000000), (301304496385036106048881/500000000000000000000000), (6539552844321447/1000000000000000000000000)⟩ else
  if n = 14617 then ⟨(552880152424314609881/500000000000000000000000), (150649638645789740431941/250000000000000000000000), (6538389634565809/1000000000000000000000000)⟩ else
  if n = 14618 then ⟨(1105733093200489785817/1000000000000000000000000), (150647029452768570871021/250000000000000000000000), (1634306678505539/250000000000000000000000)⟩ else
  if n = 14619 then ⟨(552852943889410864501/500000000000000000000000), (602577682453511791796281/1000000000000000000000000), (3268032041299093/500000000000000000000000)⟩ else
  if n = 14620 then ⟨(1105678688581759879657/1000000000000000000000000), (301283624255082578335539/500000000000000000000000), (3267450870100807/500000000000000000000000)⟩ else
  if n = 14621 then ⟨(138206436950929972877/125000000000000000000000), (602556815980727968370429/1000000000000000000000000), (6533739686740193/1000000000000000000000000)⟩ else
  if n = 14622 then ⟨(34550759651687428089/31250000000000000000000), (150636596216223532449541/250000000000000000000000), (408286120132607/62500000000000000000000)⟩ else
  if n = 14623 then ⟨(552798564159785073427/500000000000000000000000), (18829248598823670420723/31250000000000000000000), (6531416446253981/1000000000000000000000000)⟩ else
  if n = 14624 then ⟨(276392488500573930873/250000000000000000000000), (150631381718203006533221/250000000000000000000000), (6530255259044897/1000000000000000000000000)⟩ else
  ⟨(276385696475077866953/250000000000000000000000), (75314387499493973165751/125000000000000000000000), (6529094360402309/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14551 ≤ n) (hb : n ≤ 14625) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14551
  · exact row_14552
  · exact row_14553
  · exact row_14554
  · exact row_14555
  · exact row_14556
  · exact row_14557
  · exact row_14558
  · exact row_14559
  · exact row_14560
  · exact row_14561
  · exact row_14562
  · exact row_14563
  · exact row_14564
  · exact row_14565
  · exact row_14566
  · exact row_14567
  · exact row_14568
  · exact row_14569
  · exact row_14570
  · exact row_14571
  · exact row_14572
  · exact row_14573
  · exact row_14574
  · exact row_14575
  · exact row_14576
  · exact row_14577
  · exact row_14578
  · exact row_14579
  · exact row_14580
  · exact row_14581
  · exact row_14582
  · exact row_14583
  · exact row_14584
  · exact row_14585
  · exact row_14586
  · exact row_14587
  · exact row_14588
  · exact row_14589
  · exact row_14590
  · exact row_14591
  · exact row_14592
  · exact row_14593
  · exact row_14594
  · exact row_14595
  · exact row_14596
  · exact row_14597
  · exact row_14598
  · exact row_14599
  · exact row_14600
  · exact row_14601
  · exact row_14602
  · exact row_14603
  · exact row_14604
  · exact row_14605
  · exact row_14606
  · exact row_14607
  · exact row_14608
  · exact row_14609
  · exact row_14610
  · exact row_14611
  · exact row_14612
  · exact row_14613
  · exact row_14614
  · exact row_14615
  · exact row_14616
  · exact row_14617
  · exact row_14618
  · exact row_14619
  · exact row_14620
  · exact row_14621
  · exact row_14622
  · exact row_14623
  · exact row_14624
  · exact row_14625

end BstLean.Part271.R3.Rows14551
