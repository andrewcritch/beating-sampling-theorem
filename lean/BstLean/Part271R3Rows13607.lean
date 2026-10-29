import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 13607–13681. -/
namespace BstLean.Part271.R3.Rows13607
open Real BstLean.Part130 BstLean.Part227

theorem width_13607 : mW 13607 = 293878860184922 := by
  have hu : mW 13607 ≤ 293878860184922 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13607 ≤ 293878860184921 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13607 : RowArithmetic 13607 (1136777295265164191449/1000000000000000000000000) (153479738345409529647379/250000000000000000000000) (7878173150712813/1000000000000000000000000) where
  r0 := (630023026779/1000000000000000000)
  k0 := (3752467807791381/1000000000000000000)
  k6 := (11738684861401617/1000000000000000000)
  q := (82483331649491462573/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13607]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13607]

theorem width_13608 : mW 13608 = 293954458810903 := by
  have hu : mW 13608 ≤ 293954458810903 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13608 ≤ 293954458810902 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13608 : RowArithmetic 13608 (1136742708988706570769/1000000000000000000000000) (613906914186975906170599/1000000000000000000000000) (3938332052372957/500000000000000000000000) where
  r0 := (39372098817/62500000000000000)
  k0 := (1876130494992233/500000000000000000)
  k6 := (91705105764813/7812500000000000)
  q := (82486362509205120119/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13608]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13608]

theorem width_13609 : mW 13609 = 294030071326796 := by
  have hu : mW 13609 ≤ 294030071326796 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13609 ≤ 294030071326795 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13609 : RowArithmetic 13609 (45468325249395114427/40000000000000000000000) (153473719192360330112907/250000000000000000000000) (7875155462741479/1000000000000000000000000) where
  r0 := (629884148123/1000000000000000000)
  k0 := (1876027099387763/500000000000000000)
  k6 := (11737822261932369/1000000000000000000)
  q := (164978786515115330449/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13609]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13609]

theorem width_13610 : mW 13610 = 294105697734133 := by
  have hu : mW 13610 ≤ 294105697734133 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13610 ≤ 294105697734132 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13610 : RowArithmetic 13610 (1136673562000928796769/1000000000000000000000000) (76735355141076922878669/125000000000000000000000) (314945888982427/40000000000000000000000) where
  r0 := (629814727927/1000000000000000000)
  k0 := (3751847434154067/1000000000000000000)
  k6 := (58686955167509/5000000000000000)
  q := (82492423894561372017/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13610]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13610]

theorem width_13611 : mW 13611 = 294181338034444 := by
  have hu : mW 13611 ≤ 294181338034444 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13611 ≤ 294181338034443 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13611 : RowArithmetic 13611 (11366390012841126293/10000000000000000000000) (306935403632039643026279/500000000000000000000000) (492008711879049/62500000000000000000000) where
  r0 := (629745320481/1000000000000000000)
  k0 := (937910174028887/250000000000000000)
  k6 := (1467119981574453/125000000000000000)
  q := (8249545442022851237/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13611]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13611]

theorem width_13612 : mW 13612 = 294256992229261 := by
  have hu : mW 13612 ≤ 294256992229261 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13612 ≤ 294256992229260 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13612 : RowArithmetic 13612 (1136604449081682361229/1000000000000000000000000) (306929387587707152047053/500000000000000000000000) (1967657989778773/250000000000000000000000) where
  r0 := (629675925783/1000000000000000000)
  k0 := (3751433984658407/1000000000000000000)
  k6 := (5868264359602557/500000000000000000)
  q := (32999393933828542361/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13612]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13612]

theorem width_13613 : mW 13613 = 294332660320115 := by
  have hu : mW 13613 ≤ 294332660320115 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13613 ≤ 294332660320114 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13613 : RowArithmetic 13613 (1136569905390892818479/1000000000000000000000000) (153461686215550481852649/250000000000000000000000) (7869124931572971/1000000000000000000000000) where
  r0 := (629606543829/1000000000000000000)
  k0 := (1875613649887561/500000000000000000)
  k6 := (11736097633321543/1000000000000000000)
  q := (82501515137602169979/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13613]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13613]

theorem width_13614 : mW 13614 = 294408342308537 := by
  have hu : mW 13614 ≤ 294408342308537 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13614 ≤ 294408342308536 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13614 : RowArithmetic 13614 (17758365159515624357/15625000000000000000000) (613834716324023706143711/1000000000000000000000000) (1573523661459971/200000000000000000000000) where
  r0 := (125907434923/200000000000000000)
  k0 := (3751020641458169/1000000000000000000)
  k6 := (11735666594936187/1000000000000000000)
  q := (82504545329333219713/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13614]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13614]

theorem width_13615 : mW 13615 = 294484038196059 := by
  have hu : mW 13615 ≤ 294484038196059 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13615 ≤ 294484038196058 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13615 : RowArithmetic 13615 (1136500843533260182701/1000000000000000000000000) (613822689560461380417129/1000000000000000000000000) (786611208615721/100000000000000000000000) where
  r0 := (629467818139/1000000000000000000)
  k0 := (187540700485299/50000000000000000)
  k6 := (2933808901010081/250000000000000000)
  q := (20626893852444191991/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13615]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13615]

theorem width_13616 : mW 13616 = 294559747984213 := by
  have hu : mW 13616 ≤ 294559747984213 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13616 ≤ 294559747984212 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13616 : RowArithmetic 13616 (1136466325360931022253/1000000000000000000000000) (4910485316568774527969/8000000000000000000000) (7864606268006561/1000000000000000000000000) where
  r0 := (629398474397/1000000000000000000)
  k0 := (937651851127757/250000000000000000)
  k6 := (2346960932125047/200000000000000000)
  q := (41255302689472537671/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13616]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13616]

theorem width_13617 : mW 13617 = 294635471674529 := by
  have hu : mW 13617 ≤ 294635471674529 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13617 ≤ 294635471674528 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13617 : RowArithmetic 13617 (284107953922318129301/250000000000000000000000) (613798641355511921766757/1000000000000000000000000) (1572620170541909/200000000000000000000000) where
  r0 := (314664571693/500000000000000000)
  k0 := (937600206467191/250000000000000000)
  k6 := (5867186882341101/500000000000000000)
  q := (82513635236850400203/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13617]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13617]

theorem width_13618 : mW 13618 = 294711209268539 := by
  have hu : mW 13618 ≤ 294711209268539 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13618 ≤ 294711209268538 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13618 : RowArithmetic 13618 (142049664314443057487/125000000000000000000000) (76723327489161115776677/125000000000000000000000) (122837435001997/15625000000000000000000) where
  r0 := (629259825103/1000000000000000000)
  k0 := (1875097136887317/500000000000000000)
  k6 := (11733942916202511/1000000000000000000)
  q := (165033329967009997311/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13618]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13618]

theorem width_13619 : mW 13619 = 294786960767775 := by
  have hu : mW 13619 ≤ 294786960767775 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13619 ≤ 294786960767774 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13619 : RowArithmetic 13619 (568181410918503886359/500000000000000000000000) (613774600244010007046599/1000000000000000000000000) (7860091230123053/1000000000000000000000000) where
  r0 := (78648814943/125000000000000000)
  k0 := (1874993874110553/500000000000000000)
  k6 := (1466689014397181/125000000000000000)
  q := (20629923654730281139/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13619]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13619]

theorem width_13620 : mW 13620 = 294862726173769 := by
  have hu : mW 13620 ≤ 294862726173769 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13620 ≤ 294862726173768 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13620 : RowArithmetic 13620 (454531335060369803/400000000000000000000) (613762582347257603197601/1000000000000000000000000) (3929293511278521/500000000000000000000000) where
  r0 := (125824245341/200000000000000000)
  k0 := (1874890624600323/500000000000000000)
  k6 := (5866540680799151/500000000000000000)
  q := (10315340517888878689/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13620]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13620]

theorem width_13621 : mW 13621 = 294938505488052 := by
  have hu : mW 13621 ≤ 294938505488052 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13621 ≤ 294938505488051 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13621 : RowArithmetic 13621 (71018366372159908241/62500000000000000000000) (613750566222614212223227/1000000000000000000000000) (7857083217291627/1000000000000000000000000) where
  r0 := (125810389317/200000000000000000)
  k0 := (749914955342931/200000000000000000)
  k6 := (5866325327728183/500000000000000000)
  q := (82525753556086962883/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13621]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13621]

theorem width_13622 : mW 13622 = 295014298712156 := by
  have hu : mW 13622 ≤ 295014298712156 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13622 ≤ 295014298712155 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13622 : RowArithmetic 13622 (1136259394745174153819/1000000000000000000000000) (153434637967415626236557/250000000000000000000000) (490973738386793/62500000000000000000000) where
  r0 := (628982679179/1000000000000000000)
  k0 := (749873666150523/200000000000000000)
  k6 := (11732219996742933/1000000000000000000)
  q := (165057565715722343559/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13622]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13622]

theorem width_13623 : mW 13623 = 295090105847613 := by
  have hu : mW 13623 ≤ 295090105847613 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13623 ≤ 295090105847612 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13623 : RowArithmetic 13623 (1136224936020036809061/1000000000000000000000000) (76715817410998161335043/125000000000000000000000) (7854076813110167/1000000000000000000000000) where
  r0 := (125782684897/200000000000000000)
  k0 := (937290477828237/250000000000000000)
  k6 := (117317893854493/10000000000000000)
  q := (16506362409689180213/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13623]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13623]

theorem width_13624 : mW 13624 = 295165926895955 := by
  have hu : mW 13624 ≤ 295165926895955 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13624 ≤ 295165926895954 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13624 : RowArithmetic 13624 (142023810722051632537/125000000000000000000000) (153428632119291366622647/250000000000000000000000) (490785888369879/62500000000000000000000) where
  r0 := (314422091249/500000000000000000)
  k0 := (468619439798141/125000000000000000)
  k6 := (2932839705391691/250000000000000000)
  q := (16506968225570678671/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13624]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13624]

theorem width_13625 : mW 13625 = 295241761858713 := by
  have hu : mW 13625 ≤ 295241761858713 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13625 ≤ 295241761858712 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13625 : RowArithmetic 13625 (71009752750723205153/62500000000000000000000) (306851259718393062925959/500000000000000000000000) (7851072016474467/1000000000000000000000000) where
  r0 := (2456152161/3906250000000000)
  k0 := (1874374575983787/500000000000000000)
  k6 := (5865464152543313/500000000000000000)
  q := (82537870096095889019/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13625]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13625]

theorem width_13626 : mW 13626 = 295317610737421 := by
  have hu : mW 13626 ≤ 295317610737421 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13626 ≤ 295317610737420 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13626 : RowArithmetic 13626 (35503800335086841209/31250000000000000000000) (613690512166430459983191/1000000000000000000000000) (7849570220641441/1000000000000000000000000) where
  r0 := (157176434159/250000000000000000)
  k0 := (93713570301393/25000000000000000)
  k6 := (11730497836000189/1000000000000000000)
  q := (41270449476592813091/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13626]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13626]

theorem width_13627 : mW 13627 = 295393473533609 := by
  have hu : mW 13627 ≤ 295393473533609 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13627 ≤ 295393473533608 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13627 : RowArithmetic 13627 (1136087185907307280497/1000000000000000000000000) (613678506665681809088019/1000000000000000000000000) (7848068826281219/1000000000000000000000000) where
  r0 := (628636532753/1000000000000000000)
  k0 := (3748336498639037/1000000000000000000)
  k6 := (5865033707149379/500000000000000000)
  q := (82543927699134840721/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13627]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13627]

theorem width_13628 : mW 13628 = 295469350248809 := by
  have hu : mW 13628 ≤ 295469350248809 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13628 ≤ 295469350248808 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13628 : RowArithmetic 13628 (28401319239060685797/25000000000000000000000) (306833251467061818531627/500000000000000000000000) (3923283916628019/500000000000000000000000) where
  r0 := (314283670783/500000000000000000)
  k0 := (1874065105859459/500000000000000000)
  k6 := (293240925999341/25000000000000000)
  q := (165093912667911532541/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13628]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13628]

theorem width_13629 : mW 13629 = 295545240884555 := by
  have hu : mW 13629 ≤ 295545240884555 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13629 ≤ 295545240884554 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13629 : RowArithmetic 13629 (568009180842705095853/500000000000000000000000) (613654500971339540419313/1000000000000000000000000) (7845067241428141/1000000000000000000000000) where
  r0 := (62849816307/100000000000000000)
  k0 := (3747923951284831/1000000000000000000)
  k6 := (2345841342603229/200000000000000000)
  q := (165099969715321268439/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13629]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13629]

theorem width_13630 : mW 13630 = 295621145442378 := by
  have hu : mW 13630 ≤ 295621145442378 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13630 ≤ 295621145442377 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13630 : RowArithmetic 13630 (227196792454705911507/200000000000000000000000) (613642500776913256398907/1000000000000000000000000) (980445881332489/125000000000000000000000) where
  r0 := (628428997263/1000000000000000000)
  k0 := (1873858858667593/500000000000000000)
  k6 := (2345755286683517/200000000000000000)
  q := (41276506635130836857/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13630]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13630]

theorem width_13631 : mW 13631 = 295697063923811 := by
  have hu : mW 13631 ≤ 295697063923811 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13631 ≤ 295697063923810 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13631 : RowArithmetic 13631 (70996848207753705037/62500000000000000000000) (122726100470085733671831/200000000000000000000000) (392103363040687/50000000000000000000000) where
  r0 := (628359844141/1000000000000000000)
  k0 := (149900460394497/40000000000000000)
  k6 := (11728346201169273/1000000000000000000)
  q := (82556041571771111657/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13631]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13631]

theorem width_13632 : mW 13632 = 295772996330386 := by
  have hu : mW 13632 ≤ 295772996330386 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13632 ≤ 295772996330385 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13632 : RowArithmetic 13632 (283978797208568729811/250000000000000000000000) (613618505691469814309239/1000000000000000000000000) (7840567871752097/1000000000000000000000000) where
  r0 := (628290703701/1000000000000000000)
  k0 := (149892213154479/40000000000000000)
  k6 := (469116640650501/40000000000000000)
  q := (82559069762201172709/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13632]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13632]

theorem width_13633 : mW 13633 = 295848942663635 := by
  have hu : mW 13633 ≤ 295848942663635 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13633 ≤ 295848942663634 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13633 : RowArithmetic 13633 (1135880814801453153511/1000000000000000000000000) (4793800865622037101459/7812500000000000000000) (7839068883337519/1000000000000000000000000) where
  r0 := (628221575939/1000000000000000000)
  k0 := (149883966973051/40000000000000000)
  k6 := (586374293934433/50000000000000000)
  q := (10320262230195509911/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13633]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13633]

theorem width_13634 : mW 13634 = 295924902925091 := by
  have hu : mW 13634 ≤ 295924902925091 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13634 ≤ 295924902925090 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13634 : RowArithmetic 13634 (1135846449222871101347/1000000000000000000000000) (38349657354654113620359/62500000000000000000000) (7837570295432571/1000000000000000000000000) where
  r0 := (628152460853/1000000000000000000)
  k0 := (374689304625373/100000000000000000)
  k6 := (11727055788438999/1000000000000000000)
  q := (33026050323948820629/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13634]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13634]

theorem width_13635 : mW 13635 = 296000877116286 := by
  have hu : mW 13635 ≤ 296000877116286 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13635 ≤ 296000877116285 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13635 : RowArithmetic 13635 (1135812092095807685177/1000000000000000000000000) (76697815789448671224403/125000000000000000000000) (7652414167871/976562500000000000000) where
  r0 := (628083358439/1000000000000000000)
  k0 := (149867477785471/40000000000000000)
  k6 := (2345325149100973/200000000000000000)
  q := (41284076833568653749/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13635]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13635]

theorem width_13636 : mW 13636 = 296076865238752 := by
  have hu : mW 13636 ≤ 296076865238752 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13636 ≤ 296076865238751 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13636 : RowArithmetic 13636 (35493054481798217103/31250000000000000000000) (306785268361288003704063/500000000000000000000000) (7834574320602229/1000000000000000000000000) where
  r0 := (314007134347/500000000000000000)
  k0 := (374648086947083/100000000000000000)
  k6 := (5863097874938791/500000000000000000)
  q := (82571181413372062761/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13636]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13636]

theorem width_13637 : mW 13637 = 296152867294024 := by
  have hu : mW 13637 ≤ 296152867294024 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13637 ≤ 296152867294023 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13637 : RowArithmetic 13637 (1135743403185356002511/1000000000000000000000000) (76694818611876293800859/125000000000000000000000) (1566615386680447/200000000000000000000000) where
  r0 := (125589038323/200000000000000000)
  k0 := (3746274820751309/1000000000000000000)
  k6 := (5862882900774239/500000000000000000)
  q := (82574209048588530819/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13637]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13637]

theorem width_13638 : mW 13638 = 296228883283632 := by
  have hu : mW 13638 ≤ 296228883283632 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13638 ≤ 296228883283631 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13638 : RowArithmetic 13638 (1135709071396530497619/1000000000000000000000000) (122709312566495458744557/200000000000000000000000) (1566315989232561/200000000000000000000000) where
  r0 := (627876127197/1000000000000000000)
  k0 := (1873034399233831/500000000000000000)
  k6 := (5862667950254441/500000000000000000)
  q := (82577236572798922889/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13638]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13638]

theorem width_13639 : mW 13639 = 296304913209111 := by
  have hu : mW 13639 ≤ 296304913209111 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13639 ≤ 296304913209110 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13639 : RowArithmetic 13639 (1135674748048347786817/1000000000000000000000000) (613534578534561687009699/1000000000000000000000000) (1566016671749349/200000000000000000000000) where
  r0 := (627807075439/1000000000000000000)
  k0 := (3745862802621267/1000000000000000000)
  k6 := (11724906046750127/1000000000000000000)
  q := (165160527972030895903/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13639]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13639]

theorem width_13640 : mW 13640 = 296380957071992 := by
  have hu : mW 13640 ≤ 296380957071992 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13640 ≤ 296380957071991 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13640 : RowArithmetic 13640 (567820216569046535403/500000000000000000000000) (38345162250053041028759/62500000000000000000000) (1957146792754257/250000000000000000000000) where
  r0 := (627738036337/1000000000000000000)
  k0 := (468207104150569/125000000000000000)
  k6 := (5862238120131773/500000000000000000)
  q := (33033316515300125099/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13640]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13640]

theorem width_13641 : mW 13641 = 296457014873808 := by
  have hu : mW 13641 ≤ 296457014873808 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13641 ≤ 296457014873807 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13641 : RowArithmetic 13641 (1135606126663051303841/1000000000000000000000000) (613510615230923407257919/1000000000000000000000000) (7827091382836633/1000000000000000000000000) where
  r0 := (19614656559/31250000000000000)
  k0 := (3745450890212927/1000000000000000000)
  k6 := (468961859241619/40000000000000000)
  q := (165172636959031443563/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13641]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13641]

theorem width_13642 : mW 13642 = 296533086616093 := by
  have hu : mW 13642 ≤ 296533086616093 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13642 ≤ 296533086616092 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13642 : RowArithmetic 13642 (1135571828620507876849/1000000000000000000000000) (153374659056092819406611/250000000000000000000000) (7825595994068571/1000000000000000000000000) where
  r0 := (78449999511/125000000000000000)
  k0 := (1872622486819407/500000000000000000)
  k6 := (11723616769072253/1000000000000000000)
  q := (82589345559823877321/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13642]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13642]

theorem width_13643 : mW 13643 = 296609172300379 := by
  have hu : mW 13643 ≤ 296609172300379 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13643 ≤ 296609172300378 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13643 : RowArithmetic 13643 (1135537539007750659807/1000000000000000000000000) (153371664745194430847847/250000000000000000000000) (7824101004575963/1000000000000000000000000) where
  r0 := (313765497467/500000000000000000)
  k0 := (1872519541738811/500000000000000000)
  k6 := (11723187104350221/1000000000000000000)
  q := (41296186264593489699/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13643]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13643]

theorem width_13644 : mW 13644 = 296685271928200 := by
  have hu : mW 13644 ≤ 296685271928200 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13644 ≤ 296685271928199 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13644 : RowArithmetic 13644 (567751628911033638689/500000000000000000000000) (613474683499728376105931/1000000000000000000000000) (7822606414221939/1000000000000000000000000) where
  r0 := (627462006423/1000000000000000000)
  k0 := (234052076232797/62500000000000000)
  k6 := (11722757486865721/1000000000000000000)
  q := (5162212461726076613/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13644]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13644]

theorem width_13645 : mW 13645 = 296761385501088 := by
  have hu : mW 13645 ≤ 296761385501088 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13645 ≤ 296761385501087 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13645 : RowArithmetic 13645 (45418759402429913237/40000000000000000000000) (38341419361300562913387/62500000000000000000000) (3910556111434869/500000000000000000000000) where
  r0 := (627393030551/1000000000000000000)
  k0 := (29957019058981/8000000000000000)
  k6 := (11722327916610099/1000000000000000000)
  q := (6607874090810144969/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13645]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13645]

theorem width_13646 : mW 13646 = 296837513020577 := by
  have hu : mW 13646 ≤ 296837513020577 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13646 ≤ 296837513020576 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13646 : RowArithmetic 13646 (141929340090135272059/125000000000000000000000) (122690147564721090216413/200000000000000000000000) (1563923686076521/200000000000000000000000) where
  r0 := (156831016829/250000000000000000)
  k0 := (468052696427453/125000000000000000)
  k6 := (5860949196787351/500000000000000000)
  q := (41300726385863965819/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13646]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13646]

theorem width_13647 : mW 13647 = 296913654488199 := by
  have hu : mW 13647 ≤ 296913654488199 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13647 ≤ 296913654488198 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13647 : RowArithmetic 13647 (2838501162000906611/2500000000000000000000) (613438767627703755892959/1000000000000000000000000) (7818125036623899/1000000000000000000000000) where
  r0 := (125451023343/200000000000000000)
  k0 := (3744215786861149/1000000000000000000)
  k6 := (11721468917750879/1000000000000000000)
  q := (82604479297432775477/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13647]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13647]

theorem width_13648 : mW 13648 = 296989809905488 := by
  have hu : mW 13648 ≤ 296989809905488 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13648 ≤ 296989809905487 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13648 : RowArithmetic 13648 (1135366217295881319727/1000000000000000000000000) (61342679919269001022137/100000000000000000000000) (3908316020728491/500000000000000000000000) where
  r0 := (627186178743/1000000000000000000)
  k0 := (3744010028686629/1000000000000000000)
  k6 := (11721039489129983/1000000000000000000)
  q := (82607505712253532489/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13648]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13648]

theorem width_13649 : mW 13649 = 297065979273978 := by
  have hu : mW 13649 ≤ 297065979273978 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13649 ≤ 297065979273977 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13649 : RowArithmetic 13649 (1135331978204931401953/1000000000000000000000000) (306707416259075286440247/500000000000000000000000) (1953784861186319/250000000000000000000000) where
  r0 := (313558626699/500000000000000000)
  k0 := (935951074223611/250000000000000000)
  k6 := (5860305053851683/500000000000000000)
  q := (41305266008101194651/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13649]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13649]

theorem width_13650 : mW 13650 = 297142162595202 := by
  have hu : mW 13650 ≤ 297142162595202 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13650 ≤ 297142162595201 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13650 : RowArithmetic 13650 (1135297747524807882939/1000000000000000000000000) (306701433801835903480907/500000000000000000000000) (244176476448509/31250000000000000000000) where
  r0 := (156762085169/250000000000000000)
  k0 := (3743598591477003/1000000000000000000)
  k6 := (5860090386731193/500000000000000000)
  q := (165227116418583060619/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13650]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13650]

theorem width_13651 : mW 13651 = 297218359870692 := by
  have hu : mW 13651 ≤ 297218359870692 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13651 ≤ 297218359870691 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13651 : RowArithmetic 13651 (567631762626403772433/500000000000000000000000) (153347726112210068775777/250000000000000000000000) (7812155446141609/1000000000000000000000000) where
  r0 := (313489720287/500000000000000000)
  k0 := (3743392912429699/1000000000000000000)
  k6 := (11719751486398401/1000000000000000000)
  q := (3304663371661325507/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13651]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13651]

theorem width_13652 : mW 13652 = 297294571101983 := by
  have hu : mW 13652 ≤ 297294571101983 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13652 ≤ 297294571101982 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13652 : RowArithmetic 13652 (1135229311386226246619/1000000000000000000000000) (153344735763310652719783/250000000000000000000000) (781066404397681/100000000000000000000000) where
  r0 := (62691055309/100000000000000000)
  k0 := (3743187259750907/1000000000000000000)
  k6 := (11719322246502771/1000000000000000000)
  q := (165239220525878782663/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13652]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13652]

theorem width_13653 : mW 13653 = 297370796290608 := by
  have hu : mW 13653 ≤ 297370796290608 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13653 ≤ 297370796290607 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13653 : RowArithmetic 13653 (1135195105922362315567/1000000000000000000000000) (24534679336658627120863/40000000000000000000000) (7809173039721573/1000000000000000000000000) where
  r0 := (626841678219/1000000000000000000)
  k0 := (1871490816715023/500000000000000000)
  k6 := (11718893053766859/1000000000000000000)
  q := (165245272247044937961/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13653]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13653]

theorem width_13654 : mW 13654 = 297447035438101 := by
  have hu : mW 13654 ≤ 297447035438101 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13654 ≤ 297447035438100 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13654 : RowArithmetic 13654 (1135160908858514512127/1000000000000000000000000) (306677512769048200467613/500000000000000000000000) (3903841216619807/500000000000000000000000) where
  r0 := (626772815959/1000000000000000000)
  k0 := (233923502091593/62500000000000000)
  k6 := (11718463908182031/1000000000000000000)
  q := (41312830936647273047/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13654]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13654]

theorem width_13655 : mW 13655 = 297523288545994 := by
  have hu : mW 13655 ≤ 297523288545994 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13655 ≤ 297523288545993 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13655 : RowArithmetic 13655 (141890840023998007713/125000000000000000000000) (153335767354430467416501/250000000000000000000000) (1951548056098689/250000000000000000000000) where
  r0 := (313351983153/500000000000000000)
  k0 := (1871285229924817/500000000000000000)
  k6 := (5859017404869827/500000000000000000)
  q := (165257375024535591829/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13655]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13655]

theorem width_13656 : mW 13656 = 297599555615823 := by
  have hu : mW 13656 ≤ 297599555615823 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13656 ≤ 297599555615822 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13656 : RowArithmetic 13656 (227018507984014118157/200000000000000000000000) (76666389381866157310451/125000000000000000000000) (7804702413050779/1000000000000000000000000) where
  r0 := (626635129257/1000000000000000000)
  k0 := (935591228144467/250000000000000000)
  k6 := (1464700719803887/125000000000000000)
  q := (82631713040454389457/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13656]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13656]

theorem width_13657 : mW 13657 = 297675836649121 := by
  have hu : mW 13657 ≤ 297675836649121 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13657 ≤ 297675836649120 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13657 : RowArithmetic 13657 (1135058368040076867267/1000000000000000000000000) (9583111913270405166577/15625000000000000000000) (7803212999071599/1000000000000000000000000) where
  r0 := (626566304809/1000000000000000000)
  k0 := (3742159391645571/1000000000000000000)
  k6 := (11717176754247731/1000000000000000000)
  q := (82634738457866495507/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13657]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13657]

theorem width_13658 : mW 13658 = 297752131647421 := by
  have hu : mW 13658 ≤ 297752131647421 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13658 ≤ 297752131647420 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13658 : RowArithmetic 13658 (56751210227465338353/50000000000000000000000) (4906457692803514838673/8000000000000000000000) (780172398232119/100000000000000000000000) where
  r0 := (313248746479/500000000000000000)
  k0 := (3741953897045139/1000000000000000000)
  k6 := (11716747797180931/1000000000000000000)
  q := (82637763764516280623/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13658]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13658]

theorem width_13659 : mW 13659 = 297828440612257 := by
  have hu : mW 13659 ≤ 297828440612257 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13659 ≤ 297828440612256 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13659 : RowArithmetic 13659 (1134990049445064597623/1000000000000000000000000) (24531810500316686585163/40000000000000000000000) (7800235362663557/1000000000000000000000000) where
  r0 := (313214346851/500000000000000000)
  k0 := (467718553596867/125000000000000000)
  k6 := (11716318887222073/1000000000000000000)
  q := (82640788960415909137/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13659]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13659]

theorem width_13660 : mW 13660 = 297904763545164 := by
  have hu : mW 13660 ≤ 297904763545164 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13660 ≤ 297904763545163 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13660 : RowArithmetic 13660 (1134955902724655098821/1000000000000000000000000) (76660414396415884610099/125000000000000000000000) (389937356998137/50000000000000000000000) where
  r0 := (626359907037/1000000000000000000)
  k0 := (1870771493413677/500000000000000000)
  k6 := (2343178004872507/200000000000000000)
  q := (41321907022788771577/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13660]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13660]

theorem width_13661 : mW 13661 = 297981100447674 := by
  have hu : mW 13661 ≤ 297981100447674 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13661 ≤ 297981100447673 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13661 : RowArithmetic 13661 (3546630513704331703/3125000000000000000000) (306635684795128487983517/500000000000000000000000) (3898629657041457/500000000000000000000000) where
  r0 := (3914319581/6250000000000000)
  k0 := (3741337571197767/1000000000000000000)
  k6 := (11715461208593697/1000000000000000000)
  q := (82646839020013342553/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13661]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13661]

theorem width_13662 : mW 13662 = 298057451321323 := by
  have hu : mW 13662 ≤ 298057451321323 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13662 ≤ 298057451321322 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13662 : RowArithmetic 13662 (141860954303070501853/125000000000000000000000) (613259425764294833143471/1000000000000000000000000) (3897885942444103/500000000000000000000000) where
  r0 := (156555592867/250000000000000000)
  k0 := (74822643637631/20000000000000000)
  k6 := (91523690936773/7812500000000000)
  q := (165299727767470929977/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13662]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13662]

theorem width_13663 : mW 13663 = 298133816167645 := by
  have hu : mW 13663 ≤ 298133816167645 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13663 ≤ 298133816167644 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13663 : RowArithmetic 13663 (567426756419748722583/500000000000000000000000) (153311870923257210681403/250000000000000000000000) (3897142426121429/500000000000000000000000) where
  r0 := (626153622557/1000000000000000000)
  k0 := (3740926818871087/1000000000000000000)
  k6 := (5857301859146829/500000000000000000)
  q := (165305777273512131779/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13663]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13663]

theorem width_13664 : mW 13664 = 298210194988173 := by
  have hu : mW 13664 ≤ 298210194988173 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13664 ≤ 298210194988172 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13664 : RowArithmetic 13664 (1134819399627496952811/1000000000000000000000000) (613235543376047225472549/1000000000000000000000000) (7792798216011191/1000000000000000000000000) where
  r0 := (39130305389/62500000000000000)
  k0 := (3740721482161751/1000000000000000000)
  k6 := (2928543760936307/250000000000000000)
  q := (41327956639543649231/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13664]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13664]

theorem width_13665 : mW 13665 = 298286587784441 := by
  have hu : mW 13665 ≤ 298286587784441 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13665 ≤ 298286587784440 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13665 : RowArithmetic 13665 (1134785294785873484339/1000000000000000000000000) (613223604812938426643749/1000000000000000000000000) (3895655988028781/500000000000000000000000) where
  r0 := (626016162467/1000000000000000000)
  k0 := (748103234350379/200000000000000000)
  k6 := (2928436604063261/250000000000000000)
  q := (82658937810741313687/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13665]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13665]

theorem width_13666 : mW 13666 = 298362994557984 := by
  have hu : mW 13666 ≤ 298362994557984 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13666 ≤ 298362994557983 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13666 : RowArithmetic 13666 (70921949894496151059/62500000000000000000000) (153302917000822734212853/250000000000000000000000) (7789826132246357/1000000000000000000000000) where
  r0 := (625947451281/1000000000000000000)
  k0 := (1870155443815457/500000000000000000)
  k6 := (2342663567161699/200000000000000000)
  q := (20665490557932565081/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13666]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13666]

theorem width_13667 : mW 13667 = 298439415310337 := by
  have hu : mW 13667 ≤ 298439415310337 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13667 ≤ 298439415310336 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13667 : RowArithmetic 13667 (22694342204060084657/20000000000000000000000) (306599866473346726939739/500000000000000000000000) (973542585555253/125000000000000000000000) where
  r0 := (78234844083/125000000000000000)
  k0 := (3740105629797159/1000000000000000000)
  k6 := (11712889302402977/1000000000000000000)
  q := (165329973084132569819/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13667]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13667]

theorem width_13668 : mW 13668 = 298515850043033 := by
  have hu : mW 13668 ≤ 298515850043033 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13668 ≤ 298515850043032 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13668 : RowArithmetic 13668 (1134683030456385865287/1000000000000000000000000) (613187799642734781207907/1000000000000000000000000) (7786855632509117/1000000000000000000000000) where
  r0 := (156452516653/250000000000000000)
  k0 := (3739900398243007/1000000000000000000)
  k6 := (2342492163205577/200000000000000000)
  q := (82668010741761531757/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13668]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13668]

theorem width_13669 : mW 13669 = 298592298757607 := by
  have hu : mW 13669 ≤ 298592298757607 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13669 ≤ 298592298757606 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13669 : RowArithmetic 13669 (56732447953469900153/50000000000000000000000) (613175868091003843605167/1000000000000000000000000) (3892685488156099/500000000000000000000000) where
  r0 := (312870696561/500000000000000000)
  k0 := (186984759648191/50000000000000000)
  k6 := (5856016188337309/500000000000000000)
  q := (82671034830828142961/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13669]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13669]

theorem width_13670 : mW 13670 = 298668761455594 := by
  have hu : mW 13670 ≤ 298668761455594 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13670 ≤ 298668761455593 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13670 : RowArithmetic 13670 (1134614896039356438247/1000000000000000000000000) (153290984572772423400189/250000000000000000000000) (486492919732243/62500000000000000000000) where
  r0 := (625672732191/1000000000000000000)
  k0 := (1869745006977479/500000000000000000)
  k6 := (731975249020911/62500000000000000)
  q := (165348117618556516787/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13670]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13670]

theorem width_13671 : mW 13671 = 298745238138528 := by
  have hu : mW 13671 ≤ 298745238138528 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13671 ≤ 298745238138527 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13671 : RowArithmetic 13671 (226916168272715747607/200000000000000000000000) (306576005121290764466193/500000000000000000000000) (7782402850584889/1000000000000000000000000) where
  r0 := (78200510477/125000000000000000)
  k0 := (186964243060589/50000000000000000)
  k6 := (292779390974979/25000000000000000)
  q := (82677082677124015707/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13671]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13671]

theorem width_13672 : mW 13672 = 298821728807943 := by
  have hu : mW 13672 ≤ 298821728807943 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13672 ≤ 298821728807942 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13672 : RowArithmetic 13672 (1134546795039383570569/1000000000000000000000000) (613140083945068694192923/1000000000000000000000000) (1945229845195991/250000000000000000000000) where
  r0 := (312767723997/500000000000000000)
  k0 := (934769933682411/250000000000000000)
  k6 := (5855373670329889/500000000000000000)
  q := (165360212868755100669/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13672]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13672]

theorem width_13673 : mW 13673 = 298898233465375 := by
  have hu : mW 13673 ≤ 298898233465375 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13673 ≤ 298898233465374 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13673 : RowArithmetic 13673 (35453523658252792521/31250000000000000000000) (122625631879628130998179/200000000000000000000000) (194485907654447/25000000000000000000000) where
  r0 := (7818335309/12500000000000000)
  k0 := (3738874634497927/1000000000000000000)
  k6 := (5855159544653917/500000000000000000)
  q := (8268313008105099549/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13673]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13673]

theorem width_13674 : mW 13674 = 298974752112357 := by
  have hu : mW 13674 ≤ 298974752112357 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13674 ≤ 298974752112356 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13674 : RowArithmetic 13674 (283619681858754412483/250000000000000000000000) (153279059150346735775173/250000000000000000000000) (7777953626631541/1000000000000000000000000) where
  r0 := (625398213993/1000000000000000000)
  k0 := (93466739012949/25000000000000000)
  k6 := (11709890884934739/1000000000000000000)
  q := (82686153617156482169/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13674]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13674]

theorem width_13675 : mW 13675 = 299051284750425 := by
  have hu : mW 13675 ≤ 299051284750425 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13675 ≤ 299051284750424 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13675 : RowArithmetic 13675 (45377788245979562567/40000000000000000000000) (122620863110879467670807/200000000000000000000000) (7776471342009829/1000000000000000000000000) where
  r0 := (625329615809/1000000000000000000)
  k0 := (3738464512782107/1000000000000000000)
  k6 := (11709462727531903/1000000000000000000)
  q := (165378354085412278299/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13675]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13675]

theorem width_13676 : mW 13676 = 299127831381114 := by
  have hu : mW 13676 ≤ 299127831381114 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13676 ≤ 299127831381113 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13676 : RowArithmetic 13676 (283602673301206500283/250000000000000000000000) (613092396256761705290107/1000000000000000000000000) (7774989452177713/1000000000000000000000000) where
  r0 := (156315257541/250000000000000000)
  k0 := (467282436410341/125000000000000000)
  k6 := (11709034617090741/1000000000000000000)
  q := (82692200357712092991/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13676]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13676]

theorem width_13677 : mW 13677 = 299204392005958 := by
  have hu : mW 13677 ≤ 299204392005958 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13677 ≤ 299204392005957 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13677 : RowArithmetic 13677 (56718834429917631421/50000000000000000000000) (613080478708070010787893/1000000000000000000000000) (3886753978500121/500000000000000000000000) where
  r0 := (19537264283/31250000000000000)
  k0 := (3738054496018163/1000000000000000000)
  k6 := (2927151638400667/250000000000000000)
  q := (41347611781093234019/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13677]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13677]

theorem width_13678 : mW 13678 = 299280966626492 := by
  have hu : mW 13678 ≤ 299280966626492 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13678 ≤ 299280966626491 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13678 : RowArithmetic 13678 (1134342692327393540701/1000000000000000000000000) (76633570363489046032879/125000000000000000000000) (7772026856342501/1000000000000000000000000) where
  r0 := (625123896481/1000000000000000000)
  k0 := (116807797718149/31250000000000000)
  k6 := (5854089268529551/500000000000000000)
  q := (41349123328070693209/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13678]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13678]

theorem width_13679 : mW 13679 = 299357555244252 := by
  have hu : mW 13679 ≤ 299357555244252 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13679 ≤ 299357555244251 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13679 : RowArithmetic 13679 (1134308704389273760527/1000000000000000000000000) (30652832442793950609947/50000000000000000000000) (7770546150069603/1000000000000000000000000) where
  r0 := (156263837109/250000000000000000)
  k0 := (3737644584165889/1000000000000000000)
  k6 := (1463468820931433/125000000000000000)
  q := (41350634819794484021/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13679]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13679]

theorem width_13680 : mW 13680 = 299434157860772 := by
  have hu : mW 13680 ≤ 299434157860772 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13680 ≤ 299434157860771 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13680 : RowArithmetic 13680 (45370988991252829949/40000000000000000000000) (306522368275780185747357/500000000000000000000000) (1942266459511693/250000000000000000000000) where
  r0 := (312493406459/500000000000000000)
  k0 := (373743966756887/100000000000000000)
  k6 := (468292905790847/40000000000000000)
  q := (5169018282033833163/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13680]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13680]

theorem width_13681 : mW 13681 = 299510774477587 := by
  have hu : mW 13681 ≤ 299510774477587 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13681 ≤ 299510774477586 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13681 : RowArithmetic 13681 (567120376750431196139/500000000000000000000000) (122606565198909381787091/200000000000000000000000) (1553517184027853/200000000000000000000000) where
  r0 := (624918289923/1000000000000000000)
  k0 := (1868617388591031/500000000000000000)
  k6 := (11706894769009661/1000000000000000000)
  q := (41353657637505294799/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13681]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13681]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 13607 then ⟨(1136777295265164191449/1000000000000000000000000), (153479738345409529647379/250000000000000000000000), (7878173150712813/1000000000000000000000000)⟩ else
  if n = 13608 then ⟨(1136742708988706570769/1000000000000000000000000), (613906914186975906170599/1000000000000000000000000), (3938332052372957/500000000000000000000000)⟩ else
  if n = 13609 then ⟨(45468325249395114427/40000000000000000000000), (153473719192360330112907/250000000000000000000000), (7875155462741479/1000000000000000000000000)⟩ else
  if n = 13610 then ⟨(1136673562000928796769/1000000000000000000000000), (76735355141076922878669/125000000000000000000000), (314945888982427/40000000000000000000000)⟩ else
  if n = 13611 then ⟨(11366390012841126293/10000000000000000000000), (306935403632039643026279/500000000000000000000000), (492008711879049/62500000000000000000000)⟩ else
  if n = 13612 then ⟨(1136604449081682361229/1000000000000000000000000), (306929387587707152047053/500000000000000000000000), (1967657989778773/250000000000000000000000)⟩ else
  if n = 13613 then ⟨(1136569905390892818479/1000000000000000000000000), (153461686215550481852649/250000000000000000000000), (7869124931572971/1000000000000000000000000)⟩ else
  if n = 13614 then ⟨(17758365159515624357/15625000000000000000000), (613834716324023706143711/1000000000000000000000000), (1573523661459971/200000000000000000000000)⟩ else
  if n = 13615 then ⟨(1136500843533260182701/1000000000000000000000000), (613822689560461380417129/1000000000000000000000000), (786611208615721/100000000000000000000000)⟩ else
  if n = 13616 then ⟨(1136466325360931022253/1000000000000000000000000), (4910485316568774527969/8000000000000000000000), (7864606268006561/1000000000000000000000000)⟩ else
  if n = 13617 then ⟨(284107953922318129301/250000000000000000000000), (613798641355511921766757/1000000000000000000000000), (1572620170541909/200000000000000000000000)⟩ else
  if n = 13618 then ⟨(142049664314443057487/125000000000000000000000), (76723327489161115776677/125000000000000000000000), (122837435001997/15625000000000000000000)⟩ else
  if n = 13619 then ⟨(568181410918503886359/500000000000000000000000), (613774600244010007046599/1000000000000000000000000), (7860091230123053/1000000000000000000000000)⟩ else
  if n = 13620 then ⟨(454531335060369803/400000000000000000000), (613762582347257603197601/1000000000000000000000000), (3929293511278521/500000000000000000000000)⟩ else
  if n = 13621 then ⟨(71018366372159908241/62500000000000000000000), (613750566222614212223227/1000000000000000000000000), (7857083217291627/1000000000000000000000000)⟩ else
  if n = 13622 then ⟨(1136259394745174153819/1000000000000000000000000), (153434637967415626236557/250000000000000000000000), (490973738386793/62500000000000000000000)⟩ else
  if n = 13623 then ⟨(1136224936020036809061/1000000000000000000000000), (76715817410998161335043/125000000000000000000000), (7854076813110167/1000000000000000000000000)⟩ else
  if n = 13624 then ⟨(142023810722051632537/125000000000000000000000), (153428632119291366622647/250000000000000000000000), (490785888369879/62500000000000000000000)⟩ else
  if n = 13625 then ⟨(71009752750723205153/62500000000000000000000), (306851259718393062925959/500000000000000000000000), (7851072016474467/1000000000000000000000000)⟩ else
  if n = 13626 then ⟨(35503800335086841209/31250000000000000000000), (613690512166430459983191/1000000000000000000000000), (7849570220641441/1000000000000000000000000)⟩ else
  if n = 13627 then ⟨(1136087185907307280497/1000000000000000000000000), (613678506665681809088019/1000000000000000000000000), (7848068826281219/1000000000000000000000000)⟩ else
  if n = 13628 then ⟨(28401319239060685797/25000000000000000000000), (306833251467061818531627/500000000000000000000000), (3923283916628019/500000000000000000000000)⟩ else
  if n = 13629 then ⟨(568009180842705095853/500000000000000000000000), (613654500971339540419313/1000000000000000000000000), (7845067241428141/1000000000000000000000000)⟩ else
  if n = 13630 then ⟨(227196792454705911507/200000000000000000000000), (613642500776913256398907/1000000000000000000000000), (980445881332489/125000000000000000000000)⟩ else
  if n = 13631 then ⟨(70996848207753705037/62500000000000000000000), (122726100470085733671831/200000000000000000000000), (392103363040687/50000000000000000000000)⟩ else
  if n = 13632 then ⟨(283978797208568729811/250000000000000000000000), (613618505691469814309239/1000000000000000000000000), (7840567871752097/1000000000000000000000000)⟩ else
  if n = 13633 then ⟨(1135880814801453153511/1000000000000000000000000), (4793800865622037101459/7812500000000000000000), (7839068883337519/1000000000000000000000000)⟩ else
  if n = 13634 then ⟨(1135846449222871101347/1000000000000000000000000), (38349657354654113620359/62500000000000000000000), (7837570295432571/1000000000000000000000000)⟩ else
  if n = 13635 then ⟨(1135812092095807685177/1000000000000000000000000), (76697815789448671224403/125000000000000000000000), (7652414167871/976562500000000000000)⟩ else
  if n = 13636 then ⟨(35493054481798217103/31250000000000000000000), (306785268361288003704063/500000000000000000000000), (7834574320602229/1000000000000000000000000)⟩ else
  if n = 13637 then ⟨(1135743403185356002511/1000000000000000000000000), (76694818611876293800859/125000000000000000000000), (1566615386680447/200000000000000000000000)⟩ else
  if n = 13638 then ⟨(1135709071396530497619/1000000000000000000000000), (122709312566495458744557/200000000000000000000000), (1566315989232561/200000000000000000000000)⟩ else
  if n = 13639 then ⟨(1135674748048347786817/1000000000000000000000000), (613534578534561687009699/1000000000000000000000000), (1566016671749349/200000000000000000000000)⟩ else
  if n = 13640 then ⟨(567820216569046535403/500000000000000000000000), (38345162250053041028759/62500000000000000000000), (1957146792754257/250000000000000000000000)⟩ else
  if n = 13641 then ⟨(1135606126663051303841/1000000000000000000000000), (613510615230923407257919/1000000000000000000000000), (7827091382836633/1000000000000000000000000)⟩ else
  if n = 13642 then ⟨(1135571828620507876849/1000000000000000000000000), (153374659056092819406611/250000000000000000000000), (7825595994068571/1000000000000000000000000)⟩ else
  if n = 13643 then ⟨(1135537539007750659807/1000000000000000000000000), (153371664745194430847847/250000000000000000000000), (7824101004575963/1000000000000000000000000)⟩ else
  if n = 13644 then ⟨(567751628911033638689/500000000000000000000000), (613474683499728376105931/1000000000000000000000000), (7822606414221939/1000000000000000000000000)⟩ else
  if n = 13645 then ⟨(45418759402429913237/40000000000000000000000), (38341419361300562913387/62500000000000000000000), (3910556111434869/500000000000000000000000)⟩ else
  if n = 13646 then ⟨(141929340090135272059/125000000000000000000000), (122690147564721090216413/200000000000000000000000), (1563923686076521/200000000000000000000000)⟩ else
  if n = 13647 then ⟨(2838501162000906611/2500000000000000000000), (613438767627703755892959/1000000000000000000000000), (7818125036623899/1000000000000000000000000)⟩ else
  if n = 13648 then ⟨(1135366217295881319727/1000000000000000000000000), (61342679919269001022137/100000000000000000000000), (3908316020728491/500000000000000000000000)⟩ else
  if n = 13649 then ⟨(1135331978204931401953/1000000000000000000000000), (306707416259075286440247/500000000000000000000000), (1953784861186319/250000000000000000000000)⟩ else
  if n = 13650 then ⟨(1135297747524807882939/1000000000000000000000000), (306701433801835903480907/500000000000000000000000), (244176476448509/31250000000000000000000)⟩ else
  if n = 13651 then ⟨(567631762626403772433/500000000000000000000000), (153347726112210068775777/250000000000000000000000), (7812155446141609/1000000000000000000000000)⟩ else
  if n = 13652 then ⟨(1135229311386226246619/1000000000000000000000000), (153344735763310652719783/250000000000000000000000), (781066404397681/100000000000000000000000)⟩ else
  if n = 13653 then ⟨(1135195105922362315567/1000000000000000000000000), (24534679336658627120863/40000000000000000000000), (7809173039721573/1000000000000000000000000)⟩ else
  if n = 13654 then ⟨(1135160908858514512127/1000000000000000000000000), (306677512769048200467613/500000000000000000000000), (3903841216619807/500000000000000000000000)⟩ else
  if n = 13655 then ⟨(141890840023998007713/125000000000000000000000), (153335767354430467416501/250000000000000000000000), (1951548056098689/250000000000000000000000)⟩ else
  if n = 13656 then ⟨(227018507984014118157/200000000000000000000000), (76666389381866157310451/125000000000000000000000), (7804702413050779/1000000000000000000000000)⟩ else
  if n = 13657 then ⟨(1135058368040076867267/1000000000000000000000000), (9583111913270405166577/15625000000000000000000), (7803212999071599/1000000000000000000000000)⟩ else
  if n = 13658 then ⟨(56751210227465338353/50000000000000000000000), (4906457692803514838673/8000000000000000000000), (780172398232119/100000000000000000000000)⟩ else
  if n = 13659 then ⟨(1134990049445064597623/1000000000000000000000000), (24531810500316686585163/40000000000000000000000), (7800235362663557/1000000000000000000000000)⟩ else
  if n = 13660 then ⟨(1134955902724655098821/1000000000000000000000000), (76660414396415884610099/125000000000000000000000), (389937356998137/50000000000000000000000)⟩ else
  if n = 13661 then ⟨(3546630513704331703/3125000000000000000000), (306635684795128487983517/500000000000000000000000), (3898629657041457/500000000000000000000000)⟩ else
  if n = 13662 then ⟨(141860954303070501853/125000000000000000000000), (613259425764294833143471/1000000000000000000000000), (3897885942444103/500000000000000000000000)⟩ else
  if n = 13663 then ⟨(567426756419748722583/500000000000000000000000), (153311870923257210681403/250000000000000000000000), (3897142426121429/500000000000000000000000)⟩ else
  if n = 13664 then ⟨(1134819399627496952811/1000000000000000000000000), (613235543376047225472549/1000000000000000000000000), (7792798216011191/1000000000000000000000000)⟩ else
  if n = 13665 then ⟨(1134785294785873484339/1000000000000000000000000), (613223604812938426643749/1000000000000000000000000), (3895655988028781/500000000000000000000000)⟩ else
  if n = 13666 then ⟨(70921949894496151059/62500000000000000000000), (153302917000822734212853/250000000000000000000000), (7789826132246357/1000000000000000000000000)⟩ else
  if n = 13667 then ⟨(22694342204060084657/20000000000000000000000), (306599866473346726939739/500000000000000000000000), (973542585555253/125000000000000000000000)⟩ else
  if n = 13668 then ⟨(1134683030456385865287/1000000000000000000000000), (613187799642734781207907/1000000000000000000000000), (7786855632509117/1000000000000000000000000)⟩ else
  if n = 13669 then ⟨(56732447953469900153/50000000000000000000000), (613175868091003843605167/1000000000000000000000000), (3892685488156099/500000000000000000000000)⟩ else
  if n = 13670 then ⟨(1134614896039356438247/1000000000000000000000000), (153290984572772423400189/250000000000000000000000), (486492919732243/62500000000000000000000)⟩ else
  if n = 13671 then ⟨(226916168272715747607/200000000000000000000000), (306576005121290764466193/500000000000000000000000), (7782402850584889/1000000000000000000000000)⟩ else
  if n = 13672 then ⟨(1134546795039383570569/1000000000000000000000000), (613140083945068694192923/1000000000000000000000000), (1945229845195991/250000000000000000000000)⟩ else
  if n = 13673 then ⟨(35453523658252792521/31250000000000000000000), (122625631879628130998179/200000000000000000000000), (194485907654447/25000000000000000000000)⟩ else
  if n = 13674 then ⟨(283619681858754412483/250000000000000000000000), (153279059150346735775173/250000000000000000000000), (7777953626631541/1000000000000000000000000)⟩ else
  if n = 13675 then ⟨(45377788245979562567/40000000000000000000000), (122620863110879467670807/200000000000000000000000), (7776471342009829/1000000000000000000000000)⟩ else
  if n = 13676 then ⟨(283602673301206500283/250000000000000000000000), (613092396256761705290107/1000000000000000000000000), (7774989452177713/1000000000000000000000000)⟩ else
  if n = 13677 then ⟨(56718834429917631421/50000000000000000000000), (613080478708070010787893/1000000000000000000000000), (3886753978500121/500000000000000000000000)⟩ else
  if n = 13678 then ⟨(1134342692327393540701/1000000000000000000000000), (76633570363489046032879/125000000000000000000000), (7772026856342501/1000000000000000000000000)⟩ else
  if n = 13679 then ⟨(1134308704389273760527/1000000000000000000000000), (30652832442793950609947/50000000000000000000000), (7770546150069603/1000000000000000000000000)⟩ else
  if n = 13680 then ⟨(45370988991252829949/40000000000000000000000), (306522368275780185747357/500000000000000000000000), (1942266459511693/250000000000000000000000)⟩ else
  ⟨(567120376750431196139/500000000000000000000000), (122606565198909381787091/200000000000000000000000), (1553517184027853/200000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 13607 ≤ n) (hb : n ≤ 13681) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_13607
  · exact row_13608
  · exact row_13609
  · exact row_13610
  · exact row_13611
  · exact row_13612
  · exact row_13613
  · exact row_13614
  · exact row_13615
  · exact row_13616
  · exact row_13617
  · exact row_13618
  · exact row_13619
  · exact row_13620
  · exact row_13621
  · exact row_13622
  · exact row_13623
  · exact row_13624
  · exact row_13625
  · exact row_13626
  · exact row_13627
  · exact row_13628
  · exact row_13629
  · exact row_13630
  · exact row_13631
  · exact row_13632
  · exact row_13633
  · exact row_13634
  · exact row_13635
  · exact row_13636
  · exact row_13637
  · exact row_13638
  · exact row_13639
  · exact row_13640
  · exact row_13641
  · exact row_13642
  · exact row_13643
  · exact row_13644
  · exact row_13645
  · exact row_13646
  · exact row_13647
  · exact row_13648
  · exact row_13649
  · exact row_13650
  · exact row_13651
  · exact row_13652
  · exact row_13653
  · exact row_13654
  · exact row_13655
  · exact row_13656
  · exact row_13657
  · exact row_13658
  · exact row_13659
  · exact row_13660
  · exact row_13661
  · exact row_13662
  · exact row_13663
  · exact row_13664
  · exact row_13665
  · exact row_13666
  · exact row_13667
  · exact row_13668
  · exact row_13669
  · exact row_13670
  · exact row_13671
  · exact row_13672
  · exact row_13673
  · exact row_13674
  · exact row_13675
  · exact row_13676
  · exact row_13677
  · exact row_13678
  · exact row_13679
  · exact row_13680
  · exact row_13681

end BstLean.Part271.R3.Rows13607
