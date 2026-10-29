import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15130–15204. -/
namespace BstLean.Part271.R3.Rows15130
open Real BstLean.Part130 BstLean.Part227

theorem width_15130 : mW 15130 = 426026140818260 := by
  have hu : mW 15130 ≤ 426026140818260 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15130 ≤ 426026140818259 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15130 : RowArithmetic 15130 (546289300575932408649/500000000000000000000000) (4779389227402052328903/8000000000000000000000) (5977814532909319/1000000000000000000000000) where
  r0 := (33583165161/62500000000000000)
  k0 := (3465449445825693/1000000000000000000)
  k6 := (1391525550454517/125000000000000000)
  q := (173954016912516280071/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15130]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15130]

theorem width_15131 : mW 15131 = 426124700942974 := by
  have hu : mW 15131 ≤ 426124700942974 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15131 ≤ 426124700942973 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15131 : RowArithmetic 15131 (546277176677236126441/500000000000000000000000) (59741390401033354971993/100000000000000000000000) (5976788570978999/1000000000000000000000000) where
  r0 := (268638687799/500000000000000000)
  k0 := (3465277672079873/1000000000000000000)
  k6 := (11131836536729119/1000000000000000000)
  q := (173959765463166798327/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15131]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15131]

theorem width_15132 : mW 15132 = 426223277353502 := by
  have hu : mW 15132 ≤ 426223277353502 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15132 ≤ 426223277353501 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15132 : RowArithmetic 15132 (218506022182199118353/200000000000000000000000) (298702077931997039000497/500000000000000000000000) (5975762855202673/1000000000000000000000000) where
  r0 := (26861205871/50000000000000000)
  k0 := (1732552959099447/500000000000000000)
  k6 := (11131468706288497/1000000000000000000)
  q := (173965513823861078493/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15132]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15132]

theorem width_15133 : mW 15133 = 426321870051460 := by
  have hu : mW 15133 ≤ 426321870051460 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15133 ≤ 426321870051459 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15133 : RowArithmetic 15133 (546252936909943254907/500000000000000000000000) (23895776359438971559389/40000000000000000000000) (1493684346376123/250000000000000000000000) where
  r0 := (537170868041/1000000000000000000)
  k0 := (3464934184182487/1000000000000000000)
  k6 := (2226220182461649/200000000000000000)
  q := (173971261994617950177/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15133]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15133]

theorem width_15134 : mW 15134 = 426420479038462 := by
  have hu : mW 15134 ≤ 426420479038462 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15134 ≤ 426420479038461 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15134 : RowArithmetic 15134 (218496328415919600037/200000000000000000000000) (597384663376010358603237/1000000000000000000000000) (2986856080904331/500000000000000000000000) where
  r0 := (537117627457/1000000000000000000)
  k0 := (1732381235010351/500000000000000000)
  k6 := (11130733154782339/1000000000000000000)
  q := (86988504987728119939/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15134]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15134]

theorem width_15135 : mW 15135 = 426519104316123 := by
  have hu : mW 15135 ≤ 426519104316123 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15135 ≤ 426519104316122 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15135 : RowArithmetic 15135 (1092457415688583256271/1000000000000000000000000) (37335932439614917620483/62500000000000000000000) (373292949002463/62500000000000000000000) where
  r0 := (134266098917/250000000000000000)
  k0 := (866147693929123/250000000000000000)
  k6 := (11130365433704759/1000000000000000000)
  q := (34796551553278954197/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15135]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15135]

theorem width_15136 : mW 15136 = 426617745886058 := by
  have hu : mW 15136 ≤ 426617745886058 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15136 ≤ 426617745886057 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15136 : RowArithmetic 15136 (4267317166583187671/3906250000000000000000) (597365175959195625662437/1000000000000000000000000) (5971662452120981/1000000000000000000000000) where
  r0 := (53701117267/100000000000000000)
  k0 := (3464419101259907/1000000000000000000)
  k6 := (11129997749069483/1000000000000000000)
  q := (173988505367452363779/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15136]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15136]

theorem width_15137 : mW 15137 = 426716403749881 := by
  have hu : mW 15137 ≤ 426716403749881 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15137 ≤ 426716403749880 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15137 : RowArithmetic 15137 (273102244737047767987/250000000000000000000000) (59735543415181760313929/100000000000000000000000) (5970637965977679/1000000000000000000000000) where
  r0 := (536957958463/1000000000000000000)
  k0 := (1732123723326949/500000000000000000)
  k6 := (5564815050435247/500000000000000000)
  q := (173994252778647835429/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15137]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15137]

theorem width_15138 : mW 15138 = 426815077909206 := by
  have hu : mW 15138 ≤ 426815077909206 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15138 ≤ 426815077909205 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15138 : RowArithmetic 15138 (109238476859572362123/100000000000000000000000) (74668211701430149235017/125000000000000000000000) (238784549021353/40000000000000000000000) where
  r0 := (134226188261/250000000000000000)
  k0 := (1732037905945869/500000000000000000)
  k6 := (11129262489101773/1000000000000000000)
  q := 174
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15138]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15138]

theorem width_15139 : mW 15139 = 426913768365650 := by
  have hu : mW 15139 ≤ 426913768365650 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15139 ≤ 426913768365649 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15139 : RowArithmetic 15139 (1092360563586348429347/1000000000000000000000000) (597335954337802960723329/1000000000000000000000000) (5968589730713733/1000000000000000000000000) where
  r0 := (536851556411/1000000000000000000)
  k0 := (865976049242481/250000000000000000)
  k6 := (2225778982751461/200000000000000000)
  q := (174005747031527668449/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15139]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15139]

theorem width_15140 : mW 15140 = 427012475120826 := by
  have hu : mW 15140 ≤ 427012475120826 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15140 ≤ 427012475120825 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15140 : RowArithmetic 15140 (43693454556740891627/40000000000000000000000) (597326216330639647292041/1000000000000000000000000) (2983782990720899/500000000000000000000000) where
  r0 := (536798368561/1000000000000000000)
  k0 := (1731866300940863/500000000000000000)
  k6 := (445141094993243/40000000000000000)
  q := (10875718367078103039/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15140]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15140]

theorem width_15141 : mW 15141 = 427111198176350 := by
  have hu : mW 15141 ≤ 427111198176350 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15141 ≤ 427111198176349 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15141 : RowArithmetic 15141 (109231216959070145661/100000000000000000000000) (119463295917937597878531/200000000000000000000000) (5966542477642407/1000000000000000000000000) where
  r0 := (268372594747/500000000000000000)
  k0 := (3463561026630093/1000000000000000000)
  k6 := (11128159872317069/1000000000000000000)
  q := (174017240525184745271/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15141]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15141]

theorem width_15142 : mW 15142 = 427209937533836 := by
  have hu : mW 15142 ≤ 427209937533836 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15142 ≤ 427209937533835 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15142 : RowArithmetic 15142 (546143990300671745683/500000000000000000000000) (37331671507167799753927/62500000000000000000000) (5965519219240001/1000000000000000000000000) where
  r0 := (536692019207/1000000000000000000)
  k0 := (865847367802073/250000000000000000)
  k6 := (2781948101552319/250000000000000000)
  q := (174022986987351760029/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15142]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15142]

theorem width_15143 : mW 15143 = 427308693194900 := by
  have hu : mW 15143 ≤ 427308693194900 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15143 ≤ 427308693194899 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15143 : RowArithmetic 15143 (218452759389781157541/200000000000000000000000) (597297009905367052639153/1000000000000000000000000) (5964496206159021/1000000000000000000000000) where
  r0 := (536638857697/1000000000000000000)
  k0 := (346321793560959/100000000000000000)
  k6 := (2225484995300337/200000000000000000)
  q := (87014366629884745717/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15143]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15143]

theorem width_15144 : mW 15144 = 427407465161157 := by
  have hu : mW 15144 ≤ 427407465161157 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15144 ≤ 427407465161156 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15144 : RowArithmetic 15144 (109223961863184667959/100000000000000000000000) (298643638480735827067037/500000000000000000000000) (1490868359580989/250000000000000000000000) where
  r0 := (134146426241/250000000000000000)
  k0 := (1731523209918467/500000000000000000)
  k6 := (11127057583188287/1000000000000000000)
  q := (87017239671228367459/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15144]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15144]

theorem width_15145 : mW 15145 = 427506253434221 := by
  have hu : mW 15145 ≤ 427506253434221 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15145 ≤ 427506253434220 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15145 : RowArithmetic 15145 (2730538614121563603/2500000000000000000000) (59727754528273573222737/100000000000000000000000) (5962450915659333/1000000000000000000000000) where
  r0 := (134133140251/250000000000000000)
  k0 := (3462874923880359/1000000000000000000)
  k6 := (445067609050523/40000000000000000)
  q := (174040225235432282809/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15145]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15145]

theorem width_15146 : mW 15146 = 427605058015709 := by
  have hu : mW 15146 ≤ 427605058015709 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15146 ≤ 427605058015708 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15146 : RowArithmetic 15146 (546095638998850402541/500000000000000000000000) (597267814868896373980067/1000000000000000000000000) (5961428638089669/1000000000000000000000000) where
  r0 := (67059928227/125000000000000000)
  k0 := (54104741370931/15625000000000000)
  k6 := (11126322905720041/1000000000000000000)
  q := (10877873183669682771/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15146]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15146]

theorem width_15147 : mW 15147 = 427703878907235 := by
  have hu : mW 15147 ≤ 427703878907235 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15147 ≤ 427703878907234 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15147 : RowArithmetic 15147 (54608355783876659223/50000000000000000000000) (119451617143938167349809/200000000000000000000000) (5960406605539551/1000000000000000000000000) where
  r0 := (268213149699/500000000000000000)
  k0 := (1731265995705549/500000000000000000)
  k6 := (5562977810776591/500000000000000000)
  q := (174051716452323445623/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15147]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15147]

theorem width_15148 : mW 15148 = 427802716110414 := by
  have hu : mW 15148 ≤ 427802716110414 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15148 ≤ 427802716110413 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15148 : RowArithmetic 15148 (136517869835822898887/125000000000000000000000) (74656044729357046998223/125000000000000000000000) (2979692408966791/500000000000000000000000) where
  r0 := (536373181747/1000000000000000000)
  k0 := (3462360554888161/1000000000000000000)
  k6 := (11125588373756493/1000000000000000000)
  q := (87028730888138314849/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15148]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15148]

theorem width_15149 : mW 15149 = 427901569626863 := by
  have hu : mW 15149 ≤ 427901569626863 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15149 ≤ 427901569626862 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15149 : RowArithmetic 15149 (546059403511655632971/500000000000000000000000) (597238631214130312809273/1000000000000000000000000) (1191672655039273/200000000000000000000000) where
  r0 := (268160036431/500000000000000000)
  k0 := (432773642271311/125000000000000000)
  k6 := (11125221162323973/1000000000000000000)
  q := (174063206910593256483/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15149]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15149]

theorem width_15150 : mW 15150 = 428000439458196 := by
  have hu : mW 15150 ≤ 428000439458196 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15150 ≤ 428000439458195 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15150 : RowArithmetic 15150 (1092094660686179528533/1000000000000000000000000) (597228905857250196317551/1000000000000000000000000) (2978670988626287/500000000000000000000000) where
  r0 := (536266972741/1000000000000000000)
  k0 := (865504435313641/250000000000000000)
  k6 := (556242699362481/50000000000000000)
  q := (21758618981911512851/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15150]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15150]

theorem width_15151 : mW 15151 = 428099325606029 := by
  have hu : mW 15151 ≤ 428099325606029 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15151 ≤ 428099325606028 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15151 : RowArithmetic 15151 (136508814959206240881/125000000000000000000000) (298609590881976718193223/500000000000000000000000) (2978160462013443/500000000000000000000000) where
  r0 := (268106940691/500000000000000000)
  k0 := (5538954182619/1600000000000000)
  k6 := (2781121712131859/250000000000000000)
  q := (87037348305195971199/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15151]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15151]

theorem width_15152 : mW 15152 = 428198228071978 := by
  have hu : mW 15152 ≤ 428198228071978 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15152 ≤ 428198228071977 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15152 : RowArithmetic 15152 (273011595996046244547/250000000000000000000000) (298604729466988841303799/500000000000000000000000) (1488825028861001/250000000000000000000000) where
  r0 := (268080399391/500000000000000000)
  k0 := (3461675006810677/1000000000000000000)
  k6 := (11124119746151421/1000000000000000000)
  q := (34816088235182309177/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15152]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15152]

theorem width_15153 : mW 15153 = 428297146857657 := by
  have hu : mW 15153 ≤ 428297146857657 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15153 ≤ 428297146857656 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15153 : RowArithmetic 15153 (546011126808124252677/500000000000000000000000) (597199737367060557427773/1000000000000000000000000) (5954279551428691/1000000000000000000000000) where
  r0 := (26805386247/50000000000000000)
  k0 := (3461503669275681/1000000000000000000)
  k6 := (556187634005779/50000000000000000)
  q := (174086185551869680801/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15153]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15153]

theorem width_15154 : mW 15154 = 428396081964683 := by
  have hu : mW 15154 ≤ 428396081964683 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15154 ≤ 428396081964682 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15154 : RowArithmetic 15154 (1091998128568303791549/1000000000000000000000000) (298595008531469909878943/500000000000000000000000) (1190651846381139/200000000000000000000000) where
  r0 := (268027329927/500000000000000000)
  k0 := (216333271970523/62500000000000000)
  k6 := (11123385650413917/1000000000000000000)
  q := (5440372804321409737/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15154]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15154]

theorem width_15155 : mW 15155 = 428495033394671 := by
  have hu : mW 15155 ≤ 428495033394671 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15155 ≤ 428495033394670 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15155 : RowArithmetic 15155 (1091974008838815425931/1000000000000000000000000) (9330942156583644230241/15625000000000000000000) (5952239156799821/1000000000000000000000000) where
  r0 := (536001603521/1000000000000000000)
  k0 := (3461161053561991/1000000000000000000)
  k6 := (11123018657040439/1000000000000000000)
  q := (87048836867588299787/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15155]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15155]

theorem width_15156 : mW 15156 = 428594001149238 := by
  have hu : mW 15156 ≤ 428594001149238 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15156 ≤ 428594001149237 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15156 : RowArithmetic 15156 (218389978885249565387/200000000000000000000000) (37323161265127418929687/62500000000000000000000) (5951219326035877/1000000000000000000000000) where
  r0 := (535948555939/1000000000000000000)
  k0 := (346098977537303/100000000000000000)
  k6 := (11122651699989153/1000000000000000000)
  q := (87051708771281451509/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15156]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15156]

theorem width_15157 : mW 15157 = 428692985229998 := by
  have hu : mW 15157 ≤ 428692985229998 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15157 ≤ 428692985229997 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15157 : RowArithmetic 15157 (1091925785329067086697/1000000000000000000000000) (597160863724734253998869/1000000000000000000000000) (297509986976937/50000000000000000000000) where
  r0 := (133973879277/250000000000000000)
  k0 := (3460818516964419/1000000000000000000)
  k6 := (11122284779254067/1000000000000000000)
  q := (174109161160462777069/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15157]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15157]

theorem width_15158 : mW 15158 = 428791985638567 := by
  have hu : mW 15158 ≤ 428791985638567 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15158 ≤ 428791985638566 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15158 : RowArithmetic 15158 (1091901681545739126089/1000000000000000000000000) (597151148469177851224221/1000000000000000000000000) (743647549654161/125000000000000000000000) where
  r0 := (535842487023/1000000000000000000)
  k0 := (432580909790369/125000000000000000)
  k6 := (11121917894829193/1000000000000000000)
  q := (34822980917778994757/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15158]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15158]

theorem width_15159 : mW 15159 = 428891002376563 := by
  have hu : mW 15159 ≤ 428891002376563 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15159 ≤ 428891002376562 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15159 : RowArithmetic 15159 (545938791537364847931/500000000000000000000000) (597141434475107620168773/1000000000000000000000000) (5948161299044401/1000000000000000000000000) where
  r0 := (133947366421/250000000000000000)
  k0 := (3460476059451561/1000000000000000000)
  k6 := (11121551046708541/1000000000000000000)
  q := (174120647827878242133/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15159]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15159]

theorem width_15160 : mW 15160 = 428990035445600 := by
  have hu : mW 15160 ≤ 428990035445600 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15160 ≤ 428990035445599 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15160 : RowArithmetic 15160 (1091853489914506587183/1000000000000000000000000) (597131721742261719666597/1000000000000000000000000) (1486785611224261/250000000000000000000000) where
  r0 := (535736453089/1000000000000000000)
  k0 := (3460304860346723/1000000000000000000)
  k6 := (88969473879089/8000000000000000)
  q := (87063195438715663993/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15160]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15160]

theorem width_15161 : mW 15161 = 429089084847294 := by
  have hu : mW 15161 ≤ 429089084847294 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15161 ≤ 429089084847293 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15161 : RowArithmetic 15161 (1091829402063537419989/1000000000000000000000000) (298561005135189242394453/500000000000000000000000) (5946123834716181/1000000000000000000000000) where
  r0 := (107136689847/200000000000000000)
  k0 := (3460133681001683/1000000000000000000)
  k6 := (278020436483899/25000000000000000)
  q := (10883258358598310883/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15161]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15161]

theorem width_15162 : mW 15162 = 429188150583262 := by
  have hu : mW 15162 ≤ 429188150583262 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15162 ≤ 429188150583261 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15162 : RowArithmetic 15162 (1091805319520290012087/1000000000000000000000000) (298556150029598079223461/500000000000000000000000) (5945105468426793/1000000000000000000000000) where
  r0 := (535630454121/1000000000000000000)
  k0 := (3459962521416143/1000000000000000000)
  k6 := (11120450720112061/1000000000000000000)
  q := (174137876408321920251/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15162]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15162]

theorem width_15163 : mW 15163 = 429287232655120 := by
  have hu : mW 15163 ≤ 429287232655120 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15163 ≤ 429287232655119 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15163 : RowArithmetic 15163 (1091781242283233115199/1000000000000000000000000) (298551295554226601261347/500000000000000000000000) (5944087345953903/1000000000000000000000000) where
  r0 := (16736795867/31250000000000000)
  k0 := (3459791381583347/1000000000000000000)
  k6 := (2224016803429689/200000000000000000)
  q := (174143618889696902957/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15163]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15163]

theorem width_15164 : mW 15164 = 429386331064483 := by
  have hu : mW 15164 ≤ 429386331064483 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15164 ≤ 429386331064482 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15164 : RowArithmetic 15164 (1091757170350836413991/1000000000000000000000000) (597092883417888086953353/1000000000000000000000000) (2971534733611289/500000000000000000000000) where
  r0 := (267762245051/500000000000000000)
  k0 := (691924052299953/200000000000000000)
  k6 := (11119717350459131/1000000000000000000)
  q := (2176867014771458197/12500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15164]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15164]

theorem width_15165 : mW 15165 = 429485445812969 := by
  have hu : mW 15165 ≤ 429485445812969 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15165 ≤ 429485445812968 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15165 : RowArithmetic 15165 (68233318982598065937/62500000000000000000000) (597083176987239366586351/1000000000000000000000000) (5942051832157869/1000000000000000000000000) where
  r0 := (267735760597/500000000000000000)
  k0 := (1729724580582549/500000000000000000)
  k6 := (11119350720038139/1000000000000000000)
  q := (43538775821099977271/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15165]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15165]

theorem width_15166 : mW 15166 = 429584576902192 := by
  have hu : mW 15166 ≤ 429584576902192 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15166 ≤ 429584576902191 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15166 : RowArithmetic 15166 (545854521196951110067/500000000000000000000000) (597073471816245695547819/1000000000000000000000000) (1188206888136983/200000000000000000000000) where
  r0 := (535418561017/1000000000000000000)
  k0 := (1729639040286293/500000000000000000)
  k6 := (1111898412587949/100000000000000000)
  q := (87080422598882695133/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15166]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15166]

theorem width_15167 : mW 15167 = 429683724333771 := by
  have hu : mW 15167 ≤ 429683724333771 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15167 ≤ 429683724333770 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15167 : RowArithmetic 15167 (1091684986366305818469/1000000000000000000000000) (597063767904645709690353/1000000000000000000000000) (5940017292728813/1000000000000000000000000) where
  r0 := (53536560957/100000000000000000)
  k0 := (1729553509860963/500000000000000000)
  k6 := (11118617567977207/1000000000000000000)
  q := (87083293460915911779/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15167]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15167]

theorem width_15168 : mW 15168 = 429782888109320 := by
  have hu : mW 15168 ≤ 429782888109320 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15168 ≤ 429782888109319 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15168 : RowArithmetic 15168 (272915233909313040113/250000000000000000000000) (597054065252178279832701/1000000000000000000000000) (5939000388214757/1000000000000000000000000) where
  r0 := (10706253337/20000000000000000)
  k0 := (691787195721271/200000000000000000)
  k6 := (5559125523162657/500000000000000000)
  q := (87086164228308965061/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15168]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15168]

theorem width_15169 : mW 15169 = 429882068230457 := by
  have hu : mW 15169 ≤ 429882068230457 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15169 ≤ 429882068230456 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15169 : RowArithmetic 15169 (1091636890205212651491/1000000000000000000000000) (298522181929291101932483/500000000000000000000000) (1484495931766979/250000000000000000000000) where
  r0 := (107051946571/200000000000000000)
  k0 := (172938247861117/50000000000000000)
  k6 := (2779471140229459/250000000000000000)
  q := (174178069802142428037/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15169]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15169]

theorem width_15170 : mW 15170 = 429981264698798 := by
  have hu : mW 15170 ≤ 429981264698798 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15170 ≤ 429981264698797 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15170 : RowArithmetic 15170 (545806425034329997711/500000000000000000000000) (1166083327585149252773/1953125000000000000000) (1484241827303379/250000000000000000000000) where
  r0 := (16725212737/31250000000000000)
  k0 := (432324244446197/125000000000000000)
  k6 := (11117518111748801/1000000000000000000)
  q := (21772976369803004037/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15170]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15170]

theorem width_15171 : mW 15171 = 430080477515959 := by
  have hu : mW 15171 ≤ 430080477515959 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15171 ≤ 430080477515958 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15171 : RowArithmetic 15171 (1091588815226067459471/1000000000000000000000000) (298512482423479954939443/500000000000000000000000) (5935951134576809/1000000000000000000000000) where
  r0 := (267576945517/500000000000000000)
  k0 := (216151435852581/62500000000000000)
  k6 := (11117151698812237/1000000000000000000)
  q := (21773693990685181851/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15171]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15171]

theorem width_15172 : mW 15172 = 430179706683557 := by
  have hu : mW 15172 ≤ 430179706683557 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15172 ≤ 430179706683556 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15172 : RowArithmetic 15172 (218312957135181701489/200000000000000000000000) (597015267228411784790777/1000000000000000000000000) (2967467601541533/500000000000000000000000) where
  r0 := (535100983203/1000000000000000000)
  k0 := (3458252011433963/1000000000000000000)
  k6 := (11116785322102173/1000000000000000000)
  q := (435488231758333511/2500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15172]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15172]

theorem width_15173 : mW 15173 = 430278952203209 := by
  have hu : mW 15173 ≤ 430278952203209 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15173 ≤ 430278952203208 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15173 : RowArithmetic 15173 (1091540761416657166567/1000000000000000000000000) (149251392716922810551263/250000000000000000000000) (2966959757328791/500000000000000000000000) where
  r0 := (535048084089/1000000000000000000)
  k0 := (86452026723601/25000000000000000)
  k6 := (69477618635079/6250000000000000)
  q := (87100516645999293407/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15173]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15173]

theorem width_15174 : mW 15174 = 430378214076532 := by
  have hu : mW 15174 ≤ 430378214076532 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15174 ≤ 430378214076531 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15174 : RowArithmetic 15174 (545758371223394013603/500000000000000000000000) (23879835030581495241051/40000000000000000000000) (1483226017306421/250000000000000000000000) where
  r0 := (534995193691/1000000000000000000)
  k0 := (1728955073085609/500000000000000000)
  k6 := (11116052677337671/1000000000000000000)
  q := (174206773691495704711/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15174]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15174]

theorem width_15175 : mW 15175 = 430477492305141 := by
  have hu : mW 15175 ≤ 430477492305141 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15175 ≤ 430477492305140 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15175 : RowArithmetic 15175 (1091492728764776974849/1000000000000000000000000) (596986181918689634020867/1000000000000000000000000) (1482972216678189/250000000000000000000000) where
  r0 := (267471156003/500000000000000000)
  k0 := (1728869621554363/500000000000000000)
  k6 := (11115686409271299/1000000000000000000)
  q := (174212513901843457671/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15175]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15175]

theorem width_15176 : mW 15176 = 430576786890655 := by
  have hu : mW 15176 ≤ 430576786890655 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15176 ≤ 430576786890654 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15176 : RowArithmetic 15176 (136433590046137374069/125000000000000000000000) (596976489329887250272751/1000000000000000000000000) (5930873907044153/1000000000000000000000000) where
  r0 := (66861179879/125000000000000000)
  k0 := (1728784179876511/500000000000000000)
  k6 := (11115320177407559/1000000000000000000)
  q := (174218253923060542193/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15176]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15176]

theorem width_15177 : mW 15177 = 430676097834689 := by
  have hu : mW 15177 ≤ 430676097834689 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15177 ≤ 430676097834688 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15177 : RowArithmetic 15177 (109144471725823109019/100000000000000000000000) (23878671919914791383981/40000000000000000000000) (2964929595072657/500000000000000000000000) where
  r0 := (33427285923/62500000000000000)
  k0 := (3457397496103797/1000000000000000000)
  k6 := (11114953981740489/1000000000000000000)
  q := (10888999609697853231/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15177]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15177]

theorem width_15178 : mW 15178 = 430775425138861 := by
  have hu : mW 15178 ≤ 430775425138861 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15178 ≤ 430775425138860 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15178 : RowArithmetic 15178 (1091420719430649741497/1000000000000000000000000) (596957107922376742372947/1000000000000000000000000) (1482211178985417/250000000000000000000000) where
  r0 := (53478371921/100000000000000000)
  k0 := (1728613326075521/500000000000000000)
  k6 := (88916702578113/8000000000000000)
  q := (174229733398177476521/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15178]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15178]

theorem width_15179 : mW 15179 = 430874768804787 := by
  have hu : mW 15179 ≤ 430874768804787 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15179 ≤ 430874768804786 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15179 : RowArithmetic 15179 (218279345376966542737/200000000000000000000000) (596947419103147653060421/1000000000000000000000000) (2963915242179349/500000000000000000000000) where
  r0 := (267365436179/500000000000000000)
  k0 := (3457055827897679/1000000000000000000)
  k6 := (2778555424743127/250000000000000000)
  q := (21779434106514337991/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15179]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15179]

theorem width_15180 : mW 15180 = 430974128834085 := by
  have hu : mW 15180 ≤ 430974128834085 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15180 ≤ 430974128834084 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15180 : RowArithmetic 15180 (68210796226203600257/62500000000000000000000) (596937731539922251640399/1000000000000000000000000) (185213015478809/31250000000000000000000) where
  r0 := (53467803421/100000000000000000)
  k0 := (3456885023340161/1000000000000000000)
  k6 := (11113855611859677/1000000000000000000)
  q := (87120606058498009051/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15180]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15180]

theorem width_15181 : mW 15181 = 431073505228372 := by
  have hu : mW 15181 ≤ 431073505228372 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15181 ≤ 431073505228371 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15181 : RowArithmetic 15181 (1091348757632402937241/1000000000000000000000000) (59692804523244026191311/100000000000000000000000) (2962901374378383/500000000000000000000000) where
  r0 := (267312602381/500000000000000000)
  k0 := (3456714238468477/1000000000000000000)
  k6 := (444539582436787/40000000000000000)
  q := (174246951192840100149/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15181]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15181]

theorem width_15182 : mW 15182 = 431172897989265 := by
  have hu : mW 15182 ≤ 431172897989265 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15182 ≤ 431172897989264 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15182 : RowArithmetic 15182 (1091324780922747798539/1000000000000000000000000) (298459180090220750530793/500000000000000000000000) (5924789244588887/1000000000000000000000000) where
  r0 := (267286192007/500000000000000000)
  k0 := (1728271736642773/500000000000000000)
  k6 := (2222624709229309/200000000000000000)
  q := (1742526900796656281/10000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15182]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15182]

theorem width_15183 : mW 15183 = 431272307118381 := by
  have hu : mW 15183 ≤ 431272307118381 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15183 ≤ 431272307118380 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15183 : RowArithmetic 15183 (34103150296524119819/31250000000000000000000) (596908676383665876708779/1000000000000000000000000) (5923775982743837/1000000000000000000000000) where
  r0 := (534519571963/1000000000000000000)
  k0 := (691274545556917/200000000000000000)
  k6 := (2778189391883583/250000000000000000)
  q := (174258428777491276909/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15183]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15183]

theorem width_15184 : mW 15184 = 431371732617337 := by
  have hu : mW 15184 ≤ 431371732617337 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15184 ≤ 431371732617336 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15184 : RowArithmetic 15184 (1091276843328955250917/1000000000000000000000000) (119379798768370662960701/200000000000000000000000) (5922762963147227/1000000000000000000000000) where
  r0 := (534466768607/1000000000000000000)
  k0 := (1728101000981023/500000000000000000)
  k6 := (11112391625077081/1000000000000000000)
  q := (21783020910791964807/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15184]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15184]

theorem width_15185 : mW 15185 = 431471174487750 := by
  have hu : mW 15185 ≤ 431471174487750 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15185 ≤ 431471174487749 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15185 : RowArithmetic 15185 (545626441220889407769/500000000000000000000000) (59688931255474391571523/100000000000000000000000) (5921750185724699/1000000000000000000000000) where
  r0 := (66801746743/125000000000000000)
  k0 := (3456031295814377/1000000000000000000)
  k6 := (5556012859384421/500000000000000000)
  q := (174269905606217621547/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15185]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15185]

theorem width_15186 : mW 15186 = 431570632731239 := by
  have hu : mW 15186 ≤ 431570632731239 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15186 ≤ 431570632731238 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15186 : RowArithmetic 15186 (545614463412861562859/500000000000000000000000) (596879632522077764057009/1000000000000000000000000) (5920737650401897/1000000000000000000000000) where
  r0 := (133590296993/250000000000000000)
  k0 := (863965152334507/250000000000000000)
  k6 := (11111659848603661/1000000000000000000)
  q := (87137821868577825957/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15186]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15186]

theorem width_15187 : mW 15187 = 431670107349419 := by
  have hu : mW 15187 ≤ 431670107349419 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15187 ≤ 431670107349418 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15187 : RowArithmetic 15187 (218240995295854159529/200000000000000000000000) (596869953743595027635137/1000000000000000000000000) (2959862678552273/500000000000000000000000) where
  r0 := (53430841069/100000000000000000)
  k0 := (1727844971266339/500000000000000000)
  k6 := (1111129401457559/100000000000000000)
  q := (21785172709896059027/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15187]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15187]

theorem width_15188 : mW 15188 = 431769598343910 := by
  have hu : mW 15188 ≤ 431769598343910 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15188 ≤ 431769598343909 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15188 : RowArithmetic 15188 (545590515700451592147/500000000000000000000000) (119372055243807204999473/200000000000000000000000) (5918713305758333/1000000000000000000000000) where
  r0 := (106851128419/200000000000000000)
  k0 := (3455519295391541/1000000000000000000)
  k6 := (277773205416967/25000000000000000)
  q := (4357177985806868551/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15188]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15188]

theorem width_15189 : mW 15189 = 431869105716327 := by
  have hu : mW 15189 ≤ 431869105716327 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15189 ≤ 431869105716326 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15189 : RowArithmetic 15189 (1091157091589104020247/1000000000000000000000000) (596850599948141044292131/1000000000000000000000000) (5917701496289041/1000000000000000000000000) where
  r0 := (106840576437/200000000000000000)
  k0 := (1727674333955531/500000000000000000)
  k6 := (1388820306863373/125000000000000000)
  q := (174292856996493117903/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15189]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15189]

theorem width_15190 : mW 15190 = 431968629468289 := by
  have hu : mW 15190 ≤ 431968629468289 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15190 ≤ 431968629468288 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15190 : RowArithmetic 15190 (1091133157042356141759/1000000000000000000000000) (29842046246532525487007/50000000000000000000000) (5916689928622427/1000000000000000000000000) where
  r0 := (267075065479/500000000000000000)
  k0 := (1727589030043843/500000000000000000)
  k6 := (11110196729254557/1000000000000000000)
  q := (2723415537060035207/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15190]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15190]

theorem width_15191 : mW 15191 = 432068169601414 := by
  have hu : mW 15191 ≤ 432068169601414 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15191 ≤ 432068169601413 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15191 : RowArithmetic 15191 (27277730693978582717/25000000000000000000000) (596831251166304919732703/1000000000000000000000000) (591567860268429/100000000000000000000000) where
  r0 := (133524347103/250000000000000000)
  k0 := (1727503735958927/500000000000000000)
  k6 := (5554915519857727/500000000000000000)
  q := (43576082889585199613/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15191]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15191]

theorem width_15192 : mW 15192 = 432167726117318 := by
  have hu : mW 15192 ≤ 432167726117318 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15192 ≤ 432167726117317 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15192 : RowArithmetic 15192 (545542651868975283619/500000000000000000000000) (298410789327422401301347/500000000000000000000000) (2957333759200243/500000000000000000000000) where
  r0 := (267022327273/500000000000000000)
  k0 := (690967380680249/200000000000000000)
  k6 := (2777366346570933/250000000000000000)
  q := (8715503427800370041/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15192]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15192]

theorem width_15193 : mW 15193 = 432267299017621 := by
  have hu : mW 15193 ≤ 432267299017621 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15193 ≤ 432267299017620 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15193 : RowArithmetic 15193 (1091061384977262066763/1000000000000000000000000) (37300744212250676607011/62500000000000000000000) (5913656675696843/1000000000000000000000000) where
  r0 := (533991929357/1000000000000000000)
  k0 := (431833294316383/125000000000000000)
  k6 := (222181995379069/20000000000000000)
  q := (17431580536486070459/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15193]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15193]

theorem width_15194 : mW 15194 = 432366888303938 := by
  have hu : mW 15194 ≤ 432366888303938 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15194 ≤ 432366888303937 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15194 : RowArithmetic 15194 (8728299771804514667/8000000000000000000000) (596802237389543683357193/1000000000000000000000000) (5912646074499287/1000000000000000000000000) where
  r0 := (533939212843/1000000000000000000)
  k0 := (431811978162969/125000000000000000)
  k6 := (11108734187718667/1000000000000000000)
  q := (174321541984919350931/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15194]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15194]

theorem width_15195 : mW 15195 = 432466493977889 := by
  have hu : mW 15195 ≤ 432466493977889 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15195 ≤ 432466493977888 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15195 : RowArithmetic 15195 (1091013563231342633001/1000000000000000000000000) (596792568635184124876079/1000000000000000000000000) (1182327142946741/200000000000000000000000) where
  r0 := (266943252501/500000000000000000)
  k0 := (863581328928937/250000000000000000)
  k6 := (2221673728514689/200000000000000000)
  q := (87163639208100988973/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15195]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15195]

theorem width_15196 : mW 15196 = 432566116041091 := by
  have hu : mW 15196 ≤ 432566116041091 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15196 ≤ 432566116041090 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15196 : RowArithmetic 15196 (545494830121541940031/500000000000000000000000) (149195725283168258891729/250000000000000000000000) (1477656399081513/250000000000000000000000) where
  r0 := (66729225729/125000000000000000)
  k0 := (345415482576349/100000000000000000)
  k6 := (5554001566755923/500000000000000000)
  q := (174333014658727220669/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15196]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15196]

theorem width_15197 : mW 15197 = 432665754495162 := by
  have hu : mW 15197 ≤ 432665754495162 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15197 ≤ 432665754495161 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15197 : RowArithmetic 15197 (545482881254637591471/500000000000000000000000) (596773234881751355749409/1000000000000000000000000) (5909615719202297/1000000000000000000000000) where
  r0 := (133445278833/250000000000000000)
  k0 := (3453984355446649/1000000000000000000)
  k6 := (5553818830263967/500000000000000000)
  q := (174338750712513711073/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15197]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15197]

theorem width_15198 : mW 15198 = 432765409341721 := by
  have hu : mW 15198 ≤ 432765409341721 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15198 ≤ 432765409341720 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15198 : RowArithmetic 15198 (1090941870028403844417/1000000000000000000000000) (298381784941080013019541/500000000000000000000000) (2954303041644213/500000000000000000000000) where
  r0 := (266864216749/500000000000000000)
  k0 := (431726738094399/125000000000000000)
  k6 := (444290888944631/40000000000000000)
  q := (8717224328879003903/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15198]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15198]

theorem width_15199 : mW 15199 = 432865080582384 := by
  have hu : mW 15199 ≤ 432865080582384 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15199 ≤ 432865080582383 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15199 : RowArithmetic 15199 (545458991399479406577/500000000000000000000000) (119350781226728035542727/200000000000000000000000) (2953798344255247/500000000000000000000000) where
  r0 := (53367576033/100000000000000000)
  k0 := (3453643473692023/1000000000000000000)
  k6 := (2221381364553887/200000000000000000)
  q := (87175111126972473737/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15199]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15199]

theorem width_15200 : mW 15200 = 432964768218770 := by
  have hu : mW 15200 ≤ 432964768218770 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15200 ≤ 432964768218769 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15200 : RowArithmetic 15200 (272723525204857126397/250000000000000000000000) (59674424363593294531323/100000000000000000000000) (5906587534794541/1000000000000000000000000) where
  r0 := (21344923833/40000000000000000)
  k0 := (1726736531125171/500000000000000000)
  k6 := (5553270728991491/500000000000000000)
  q := (17435595774162694209/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15200]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15200]

theorem width_15201 : mW 15201 = 433064472252498 := by
  have hu : mW 15201 ≤ 433064472252498 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15201 ≤ 433064472252497 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15201 : RowArithmetic 15201 (68179389005518868451/62500000000000000000000) (596734582388779555119389/1000000000000000000000000) (5905578622066639/1000000000000000000000000) where
  r0 := (266785219991/500000000000000000)
  k0 := (3453302670429817/1000000000000000000)
  k6 := (5553088064625243/500000000000000000)
  q := (174361693040644681623/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15201]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15201]

theorem width_15202 : mW 15202 = 433164192685185 := by
  have hu : mW 15202 ≤ 433164192685185 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15202 ≤ 433164192685184 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15202 : RowArithmetic 15202 (1090846352604069237027/1000000000000000000000000) (298362461195960647879433/500000000000000000000000) (2952284975126457/500000000000000000000000) where
  r0 := (533517792797/1000000000000000000)
  k0 := (431641537277551/125000000000000000)
  k6 := (11105810836566017/1000000000000000000)
  q := (87183714075508391363/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15202]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15202]

theorem width_15203 : mW 15203 = 433263929518449 := by
  have hu : mW 15203 ≤ 433263929518449 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15203 ≤ 433263929518448 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15203 : RowArithmetic 15203 (68176405397826311201/62500000000000000000000) (119343052729019898593111/200000000000000000000000) (1180712303855901/200000000000000000000000) where
  r0 := (53346515427/100000000000000000)
  k0 := (3452961945625017/1000000000000000000)
  k6 := (11105445579923647/1000000000000000000)
  q := (43593290768190464747/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15203]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15203]

theorem width_15204 : mW 15204 = 433363682753910 := by
  have hu : mW 15204 ≤ 433363682753910 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15204 ≤ 433363682753909 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15204 : RowArithmetic 15204 (1090798625370247401541/1000000000000000000000000) (298352803074027823431911/500000000000000000000000) (1475638332268139/250000000000000000000000) where
  r0 := (266706262199/500000000000000000)
  k0 := (3452791612636839/1000000000000000000)
  k6 := (11105080359317451/1000000000000000000)
  q := (174378897805898520939/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15204]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15204]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 15130 then ⟨(546289300575932408649/500000000000000000000000), (4779389227402052328903/8000000000000000000000), (5977814532909319/1000000000000000000000000)⟩ else
  if n = 15131 then ⟨(546277176677236126441/500000000000000000000000), (59741390401033354971993/100000000000000000000000), (5976788570978999/1000000000000000000000000)⟩ else
  if n = 15132 then ⟨(218506022182199118353/200000000000000000000000), (298702077931997039000497/500000000000000000000000), (5975762855202673/1000000000000000000000000)⟩ else
  if n = 15133 then ⟨(546252936909943254907/500000000000000000000000), (23895776359438971559389/40000000000000000000000), (1493684346376123/250000000000000000000000)⟩ else
  if n = 15134 then ⟨(218496328415919600037/200000000000000000000000), (597384663376010358603237/1000000000000000000000000), (2986856080904331/500000000000000000000000)⟩ else
  if n = 15135 then ⟨(1092457415688583256271/1000000000000000000000000), (37335932439614917620483/62500000000000000000000), (373292949002463/62500000000000000000000)⟩ else
  if n = 15136 then ⟨(4267317166583187671/3906250000000000000000), (597365175959195625662437/1000000000000000000000000), (5971662452120981/1000000000000000000000000)⟩ else
  if n = 15137 then ⟨(273102244737047767987/250000000000000000000000), (59735543415181760313929/100000000000000000000000), (5970637965977679/1000000000000000000000000)⟩ else
  if n = 15138 then ⟨(109238476859572362123/100000000000000000000000), (74668211701430149235017/125000000000000000000000), (238784549021353/40000000000000000000000)⟩ else
  if n = 15139 then ⟨(1092360563586348429347/1000000000000000000000000), (597335954337802960723329/1000000000000000000000000), (5968589730713733/1000000000000000000000000)⟩ else
  if n = 15140 then ⟨(43693454556740891627/40000000000000000000000), (597326216330639647292041/1000000000000000000000000), (2983782990720899/500000000000000000000000)⟩ else
  if n = 15141 then ⟨(109231216959070145661/100000000000000000000000), (119463295917937597878531/200000000000000000000000), (5966542477642407/1000000000000000000000000)⟩ else
  if n = 15142 then ⟨(546143990300671745683/500000000000000000000000), (37331671507167799753927/62500000000000000000000), (5965519219240001/1000000000000000000000000)⟩ else
  if n = 15143 then ⟨(218452759389781157541/200000000000000000000000), (597297009905367052639153/1000000000000000000000000), (5964496206159021/1000000000000000000000000)⟩ else
  if n = 15144 then ⟨(109223961863184667959/100000000000000000000000), (298643638480735827067037/500000000000000000000000), (1490868359580989/250000000000000000000000)⟩ else
  if n = 15145 then ⟨(2730538614121563603/2500000000000000000000), (59727754528273573222737/100000000000000000000000), (5962450915659333/1000000000000000000000000)⟩ else
  if n = 15146 then ⟨(546095638998850402541/500000000000000000000000), (597267814868896373980067/1000000000000000000000000), (5961428638089669/1000000000000000000000000)⟩ else
  if n = 15147 then ⟨(54608355783876659223/50000000000000000000000), (119451617143938167349809/200000000000000000000000), (5960406605539551/1000000000000000000000000)⟩ else
  if n = 15148 then ⟨(136517869835822898887/125000000000000000000000), (74656044729357046998223/125000000000000000000000), (2979692408966791/500000000000000000000000)⟩ else
  if n = 15149 then ⟨(546059403511655632971/500000000000000000000000), (597238631214130312809273/1000000000000000000000000), (1191672655039273/200000000000000000000000)⟩ else
  if n = 15150 then ⟨(1092094660686179528533/1000000000000000000000000), (597228905857250196317551/1000000000000000000000000), (2978670988626287/500000000000000000000000)⟩ else
  if n = 15151 then ⟨(136508814959206240881/125000000000000000000000), (298609590881976718193223/500000000000000000000000), (2978160462013443/500000000000000000000000)⟩ else
  if n = 15152 then ⟨(273011595996046244547/250000000000000000000000), (298604729466988841303799/500000000000000000000000), (1488825028861001/250000000000000000000000)⟩ else
  if n = 15153 then ⟨(546011126808124252677/500000000000000000000000), (597199737367060557427773/1000000000000000000000000), (5954279551428691/1000000000000000000000000)⟩ else
  if n = 15154 then ⟨(1091998128568303791549/1000000000000000000000000), (298595008531469909878943/500000000000000000000000), (1190651846381139/200000000000000000000000)⟩ else
  if n = 15155 then ⟨(1091974008838815425931/1000000000000000000000000), (9330942156583644230241/15625000000000000000000), (5952239156799821/1000000000000000000000000)⟩ else
  if n = 15156 then ⟨(218389978885249565387/200000000000000000000000), (37323161265127418929687/62500000000000000000000), (5951219326035877/1000000000000000000000000)⟩ else
  if n = 15157 then ⟨(1091925785329067086697/1000000000000000000000000), (597160863724734253998869/1000000000000000000000000), (297509986976937/50000000000000000000000)⟩ else
  if n = 15158 then ⟨(1091901681545739126089/1000000000000000000000000), (597151148469177851224221/1000000000000000000000000), (743647549654161/125000000000000000000000)⟩ else
  if n = 15159 then ⟨(545938791537364847931/500000000000000000000000), (597141434475107620168773/1000000000000000000000000), (5948161299044401/1000000000000000000000000)⟩ else
  if n = 15160 then ⟨(1091853489914506587183/1000000000000000000000000), (597131721742261719666597/1000000000000000000000000), (1486785611224261/250000000000000000000000)⟩ else
  if n = 15161 then ⟨(1091829402063537419989/1000000000000000000000000), (298561005135189242394453/500000000000000000000000), (5946123834716181/1000000000000000000000000)⟩ else
  if n = 15162 then ⟨(1091805319520290012087/1000000000000000000000000), (298556150029598079223461/500000000000000000000000), (5945105468426793/1000000000000000000000000)⟩ else
  if n = 15163 then ⟨(1091781242283233115199/1000000000000000000000000), (298551295554226601261347/500000000000000000000000), (5944087345953903/1000000000000000000000000)⟩ else
  if n = 15164 then ⟨(1091757170350836413991/1000000000000000000000000), (597092883417888086953353/1000000000000000000000000), (2971534733611289/500000000000000000000000)⟩ else
  if n = 15165 then ⟨(68233318982598065937/62500000000000000000000), (597083176987239366586351/1000000000000000000000000), (5942051832157869/1000000000000000000000000)⟩ else
  if n = 15166 then ⟨(545854521196951110067/500000000000000000000000), (597073471816245695547819/1000000000000000000000000), (1188206888136983/200000000000000000000000)⟩ else
  if n = 15167 then ⟨(1091684986366305818469/1000000000000000000000000), (597063767904645709690353/1000000000000000000000000), (5940017292728813/1000000000000000000000000)⟩ else
  if n = 15168 then ⟨(272915233909313040113/250000000000000000000000), (597054065252178279832701/1000000000000000000000000), (5939000388214757/1000000000000000000000000)⟩ else
  if n = 15169 then ⟨(1091636890205212651491/1000000000000000000000000), (298522181929291101932483/500000000000000000000000), (1484495931766979/250000000000000000000000)⟩ else
  if n = 15170 then ⟨(545806425034329997711/500000000000000000000000), (1166083327585149252773/1953125000000000000000), (1484241827303379/250000000000000000000000)⟩ else
  if n = 15171 then ⟨(1091588815226067459471/1000000000000000000000000), (298512482423479954939443/500000000000000000000000), (5935951134576809/1000000000000000000000000)⟩ else
  if n = 15172 then ⟨(218312957135181701489/200000000000000000000000), (597015267228411784790777/1000000000000000000000000), (2967467601541533/500000000000000000000000)⟩ else
  if n = 15173 then ⟨(1091540761416657166567/1000000000000000000000000), (149251392716922810551263/250000000000000000000000), (2966959757328791/500000000000000000000000)⟩ else
  if n = 15174 then ⟨(545758371223394013603/500000000000000000000000), (23879835030581495241051/40000000000000000000000), (1483226017306421/250000000000000000000000)⟩ else
  if n = 15175 then ⟨(1091492728764776974849/1000000000000000000000000), (596986181918689634020867/1000000000000000000000000), (1482972216678189/250000000000000000000000)⟩ else
  if n = 15176 then ⟨(136433590046137374069/125000000000000000000000), (596976489329887250272751/1000000000000000000000000), (5930873907044153/1000000000000000000000000)⟩ else
  if n = 15177 then ⟨(109144471725823109019/100000000000000000000000), (23878671919914791383981/40000000000000000000000), (2964929595072657/500000000000000000000000)⟩ else
  if n = 15178 then ⟨(1091420719430649741497/1000000000000000000000000), (596957107922376742372947/1000000000000000000000000), (1482211178985417/250000000000000000000000)⟩ else
  if n = 15179 then ⟨(218279345376966542737/200000000000000000000000), (596947419103147653060421/1000000000000000000000000), (2963915242179349/500000000000000000000000)⟩ else
  if n = 15180 then ⟨(68210796226203600257/62500000000000000000000), (596937731539922251640399/1000000000000000000000000), (185213015478809/31250000000000000000000)⟩ else
  if n = 15181 then ⟨(1091348757632402937241/1000000000000000000000000), (59692804523244026191311/100000000000000000000000), (2962901374378383/500000000000000000000000)⟩ else
  if n = 15182 then ⟨(1091324780922747798539/1000000000000000000000000), (298459180090220750530793/500000000000000000000000), (5924789244588887/1000000000000000000000000)⟩ else
  if n = 15183 then ⟨(34103150296524119819/31250000000000000000000), (596908676383665876708779/1000000000000000000000000), (5923775982743837/1000000000000000000000000)⟩ else
  if n = 15184 then ⟨(1091276843328955250917/1000000000000000000000000), (119379798768370662960701/200000000000000000000000), (5922762963147227/1000000000000000000000000)⟩ else
  if n = 15185 then ⟨(545626441220889407769/500000000000000000000000), (59688931255474391571523/100000000000000000000000), (5921750185724699/1000000000000000000000000)⟩ else
  if n = 15186 then ⟨(545614463412861562859/500000000000000000000000), (596879632522077764057009/1000000000000000000000000), (5920737650401897/1000000000000000000000000)⟩ else
  if n = 15187 then ⟨(218240995295854159529/200000000000000000000000), (596869953743595027635137/1000000000000000000000000), (2959862678552273/500000000000000000000000)⟩ else
  if n = 15188 then ⟨(545590515700451592147/500000000000000000000000), (119372055243807204999473/200000000000000000000000), (5918713305758333/1000000000000000000000000)⟩ else
  if n = 15189 then ⟨(1091157091589104020247/1000000000000000000000000), (596850599948141044292131/1000000000000000000000000), (5917701496289041/1000000000000000000000000)⟩ else
  if n = 15190 then ⟨(1091133157042356141759/1000000000000000000000000), (29842046246532525487007/50000000000000000000000), (5916689928622427/1000000000000000000000000)⟩ else
  if n = 15191 then ⟨(27277730693978582717/25000000000000000000000), (596831251166304919732703/1000000000000000000000000), (591567860268429/100000000000000000000000)⟩ else
  if n = 15192 then ⟨(545542651868975283619/500000000000000000000000), (298410789327422401301347/500000000000000000000000), (2957333759200243/500000000000000000000000)⟩ else
  if n = 15193 then ⟨(1091061384977262066763/1000000000000000000000000), (37300744212250676607011/62500000000000000000000), (5913656675696843/1000000000000000000000000)⟩ else
  if n = 15194 then ⟨(8728299771804514667/8000000000000000000000), (596802237389543683357193/1000000000000000000000000), (5912646074499287/1000000000000000000000000)⟩ else
  if n = 15195 then ⟨(1091013563231342633001/1000000000000000000000000), (596792568635184124876079/1000000000000000000000000), (1182327142946741/200000000000000000000000)⟩ else
  if n = 15196 then ⟨(545494830121541940031/500000000000000000000000), (149195725283168258891729/250000000000000000000000), (1477656399081513/250000000000000000000000)⟩ else
  if n = 15197 then ⟨(545482881254637591471/500000000000000000000000), (596773234881751355749409/1000000000000000000000000), (5909615719202297/1000000000000000000000000)⟩ else
  if n = 15198 then ⟨(1090941870028403844417/1000000000000000000000000), (298381784941080013019541/500000000000000000000000), (2954303041644213/500000000000000000000000)⟩ else
  if n = 15199 then ⟨(545458991399479406577/500000000000000000000000), (119350781226728035542727/200000000000000000000000), (2953798344255247/500000000000000000000000)⟩ else
  if n = 15200 then ⟨(272723525204857126397/250000000000000000000000), (59674424363593294531323/100000000000000000000000), (5906587534794541/1000000000000000000000000)⟩ else
  if n = 15201 then ⟨(68179389005518868451/62500000000000000000000), (596734582388779555119389/1000000000000000000000000), (5905578622066639/1000000000000000000000000)⟩ else
  if n = 15202 then ⟨(1090846352604069237027/1000000000000000000000000), (298362461195960647879433/500000000000000000000000), (2952284975126457/500000000000000000000000)⟩ else
  if n = 15203 then ⟨(68176405397826311201/62500000000000000000000), (119343052729019898593111/200000000000000000000000), (1180712303855901/200000000000000000000000)⟩ else
  ⟨(1090798625370247401541/1000000000000000000000000), (298352803074027823431911/500000000000000000000000), (1475638332268139/250000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15130 ≤ n) (hb : n ≤ 15204) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15130
  · exact row_15131
  · exact row_15132
  · exact row_15133
  · exact row_15134
  · exact row_15135
  · exact row_15136
  · exact row_15137
  · exact row_15138
  · exact row_15139
  · exact row_15140
  · exact row_15141
  · exact row_15142
  · exact row_15143
  · exact row_15144
  · exact row_15145
  · exact row_15146
  · exact row_15147
  · exact row_15148
  · exact row_15149
  · exact row_15150
  · exact row_15151
  · exact row_15152
  · exact row_15153
  · exact row_15154
  · exact row_15155
  · exact row_15156
  · exact row_15157
  · exact row_15158
  · exact row_15159
  · exact row_15160
  · exact row_15161
  · exact row_15162
  · exact row_15163
  · exact row_15164
  · exact row_15165
  · exact row_15166
  · exact row_15167
  · exact row_15168
  · exact row_15169
  · exact row_15170
  · exact row_15171
  · exact row_15172
  · exact row_15173
  · exact row_15174
  · exact row_15175
  · exact row_15176
  · exact row_15177
  · exact row_15178
  · exact row_15179
  · exact row_15180
  · exact row_15181
  · exact row_15182
  · exact row_15183
  · exact row_15184
  · exact row_15185
  · exact row_15186
  · exact row_15187
  · exact row_15188
  · exact row_15189
  · exact row_15190
  · exact row_15191
  · exact row_15192
  · exact row_15193
  · exact row_15194
  · exact row_15195
  · exact row_15196
  · exact row_15197
  · exact row_15198
  · exact row_15199
  · exact row_15200
  · exact row_15201
  · exact row_15202
  · exact row_15203
  · exact row_15204

end BstLean.Part271.R3.Rows15130
