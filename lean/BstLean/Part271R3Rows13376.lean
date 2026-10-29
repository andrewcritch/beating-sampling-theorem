import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 13376–13450. -/
namespace BstLean.Part271.R3.Rows13376
open Real BstLean.Part130 BstLean.Part227

theorem width_13376 : mW 13376 = 276784592069986 := by
  have hu : mW 13376 ≤ 276784592069986 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13376 ≤ 276784592069985 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13376 : RowArithmetic 13376 (572500477097588844439/500000000000000000000000) (1233497031956229005319/2000000000000000000000) (8237883484829073/1000000000000000000000000) where
  r0 := (646413785761/1000000000000000000)
  k0 := (760193346768001/200000000000000000)
  k6 := (11839612975376289/1000000000000000000)
  q := (163560386402086981619/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13376]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13376]

theorem width_13377 : mW 13377 = 276857023036334 := by
  have hu : mW 13377 ≤ 276857023036334 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13377 ≤ 276857023036333 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13377 : RowArithmetic 13377 (1144964323195037641119/1000000000000000000000000) (123347210950402117242727/200000000000000000000000) (8236277279274017/1000000000000000000000000) where
  r0 := (12926826059/20000000000000000)
  k0 := (3800753625392273/1000000000000000000)
  k6 := (11839170430924927/1000000000000000000)
  q := (3271330004753418331/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13377]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13377]

theorem width_13378 : mW 13378 = 276929467540422 := by
  have hu : mW 13378 ≤ 276929467540422 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13378 ≤ 276929467540421 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13378 : RowArithmetic 13378 (1144927701382920826327/1000000000000000000000000) (61672359540355861317121/100000000000000000000000) (4117335755683979/500000000000000000000000) where
  r0 := (161567208421/250000000000000000)
  k0 := (3800540544822197/1000000000000000000)
  k6 := (2959681984023629/250000000000000000)
  q := (163572613844738691943/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13378]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13378]

theorem width_13379 : mW 13379 = 277001925583767 := by
  have hu : mW 13379 ≤ 277001925583767 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13379 ≤ 277001925583766 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13379 : RowArithmetic 13379 (286222772188952981643/250000000000000000000000) (616711137932306848404291/1000000000000000000000000) (1646613236191573/200000000000000000000000) where
  r0 := (16154909449/25000000000000000)
  k0 := (1900163746062823/500000000000000000)
  k6 := (1479785686359473/125000000000000000)
  q := (163578727223315929553/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13379]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13379]

theorem width_13380 : mW 13380 = 277074397167887 := by
  have hu : mW 13380 ≤ 277074397167887 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13380 ≤ 277074397167886 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13380 : RowArithmetic 13380 (1144854485310696126457/1000000000000000000000000) (308349341168901837936509/500000000000000000000000) (1028932660986343/125000000000000000000000) where
  r0 := (646123935773/1000000000000000000)
  k0 := (950028616823151/250000000000000000)
  k6 := (591892154762973/50000000000000000)
  q := (40896210093357061587/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13380]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13380]

theorem width_13381 : mW 13381 = 277146882294301 := by
  have hu : mW 13381 ≤ 277146882294301 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13381 ≤ 277146882294300 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13381 : RowArithmetic 13381 (572408945522279557051/500000000000000000000000) (616686228619597642825227/1000000000000000000000000) (8229856832013639/1000000000000000000000000) where
  r0 := (646051507121/1000000000000000000)
  k0 := (949975367580469/250000000000000000)
  k6 := (5918700374618139/500000000000000000)
  q := (40897738323775313627/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13381]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13381]

theorem width_13382 : mW 13382 = 277219380964526 := by
  have hu : mW 13382 ≤ 277219380964526 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13382 ≤ 277219380964525 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13382 : RowArithmetic 13382 (1144781305954389367047/1000000000000000000000000) (308336888388618726172089/500000000000000000000000) (8228252813173719/1000000000000000000000000) where
  r0 := (161494773/250000000000000)
  k0 := (1899844250603191/500000000000000000)
  k6 := (2959239613199243/250000000000000000)
  q := (16359706598836056143/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13382]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13382]

theorem width_13383 : mW 13383 = 277291893180082 := by
  have hu : mW 13383 ≤ 277291893180082 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13383 ≤ 277291893180081 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13383 : RowArithmetic 13383 (286186182509293585421/250000000000000000000000) (123332265362054377901917/200000000000000000000000) (8226649231218133/1000000000000000000000000) where
  r0 := (129181338081/200000000000000000)
  k0 := (1899737779968051/500000000000000000)
  k6 := (11836516205932279/1000000000000000000)
  q := (40900794613307942431/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13383]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13383]

theorem width_13384 : mW 13384 = 277364418942486 := by
  have hu : mW 13384 ≤ 277364418942486 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13384 ≤ 277364418942485 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13384 : RowArithmetic 13384 (14308852041123813043/12500000000000000000000) (616648878718249990224493/1000000000000000000000000) (1028130760749273/125000000000000000000000) where
  r0 := (129166860467/200000000000000000)
  k0 := (151970505860511/40000000000000000)
  k6 := (591803700431647/50000000000000000)
  q := (8180464534487023861/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13384]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13384]

theorem width_13385 : mW 13385 = 277436958253257 := by
  have hu : mW 13385 ≤ 277436958253257 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13385 ≤ 277436958253256 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13385 : RowArithmetic 13385 (1144671605709572217861/1000000000000000000000000) (308318216250360426186657/500000000000000000000000) (128491302771081/15625000000000000000000) where
  r0 := (80720240973/125000000000000000)
  k0 := (1899524880461717/500000000000000000)
  k6 := (369863495652803/31250000000000000)
  q := (81807701348956138483/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13385]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13385]

theorem width_13386 : mW 13386 = 277509511113913 := by
  have hu : mW 13386 ≤ 277509511113913 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13386 ≤ 277509511113912 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13386 : RowArithmetic 13386 (35769845540411519819/31250000000000000000000) (7707799851965421970249/12500000000000000000000) (8221841105130539/1000000000000000000000000) where
  r0 := (2582758267/4000000000000000)
  k0 := (949709225791719/250000000000000000)
  k6 := (11835189762693293/1000000000000000000)
  q := (16362151447777275723/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13386]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13386]

theorem width_13387 : mW 13387 = 277582077525973 := by
  have hu : mW 13387 ≤ 277582077525973 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13387 ≤ 277582077525972 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13387 : RowArithmetic 13387 (114459851803768756313/100000000000000000000000) (616611545687338157135921/1000000000000000000000000) (256882477162053/31250000000000000000000) where
  r0 := (645617219229/1000000000000000000)
  k0 := (949656018309003/250000000000000000)
  k6 := (2958686928508619/250000000000000000)
  q := (163627626029347501501/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13387]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13387]

theorem width_13388 : mW 13388 = 277654657490955 := by
  have hu : mW 13388 ≤ 277654657490955 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13388 ≤ 277654657490954 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13388 : RowArithmetic 13388 (1144561987940124296961/1000000000000000000000000) (616599105090583638630597/1000000000000000000000000) (1643727573872439/200000000000000000000000) where
  r0 := (322772442609/500000000000000000)
  k0 := (1899205635563347/500000000000000000)
  k6 := (11834305714903997/1000000000000000000)
  q := (16363373735266208849/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13388]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13388]

theorem width_13389 : mW 13389 = 277727251010378 := by
  have hu : mW 13389 ≤ 277727251010378 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13389 ≤ 277727251010377 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13389 : RowArithmetic 13389 (572262733498737314361/500000000000000000000000) (123317333273303968292303/200000000000000000000000) (4108518452753807/500000000000000000000000) where
  r0 := (80684070589/125000000000000000)
  k0 := (759639699365777/200000000000000000)
  k6 := (2366772753058521/200000000000000000)
  q := (163639848447742092133/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13389]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13389]

theorem width_13390 : mW 13390 = 277799858085760 := by
  have hu : mW 13390 ≤ 277799858085760 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13390 ≤ 277799858085759 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13390 : RowArithmetic 13390 (1144488955206736371087/1000000000000000000000000) (154143557378674185554169/250000000000000000000000) (8215436377469629/1000000000000000000000000) where
  r0 := (645400257709/1000000000000000000)
  k0 := (3797985750341377/1000000000000000000)
  k6 := (11833421865191057/1000000000000000000)
  q := (163645959314613081589/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13390]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13390]

theorem width_13391 : mW 13391 = 277872478718621 := by
  have hu : mW 13391 ≤ 277872478718621 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13391 ≤ 277872478718620 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13391 : RowArithmetic 13391 (1144452452564907078051/1000000000000000000000000) (616561794534664287408089/1000000000000000000000000) (102672953563699/12500000000000000000000) where
  r0 := (129065592841/200000000000000000)
  k0 := (3797773031657073/1000000000000000000)
  k6 := (2958245003647527/250000000000000000)
  q := (32730413990660124249/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13391]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13391]

theorem width_13392 : mW 13392 = 277945112910479 := by
  have hu : mW 13392 ≤ 277945112910479 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13392 ≤ 277945112910478 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13392 : RowArithmetic 13392 (1144415959068987080893/1000000000000000000000000) (616549361425972708200139/1000000000000000000000000) (8212236628234297/1000000000000000000000000) where
  r0 := (645255684197/1000000000000000000)
  k0 := (474695042596477/125000000000000000)
  k6 := (11832538213480517/1000000000000000000)
  q := (81829090181915135357/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13392]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13392]

theorem width_13393 : mW 13393 = 278017760662853 := by
  have hu : mW 13393 ≤ 278017760662853 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13393 ≤ 278017760662852 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13393 : RowArithmetic 13393 (572189737357988605087/500000000000000000000000) (123307386037634452697437/200000000000000000000000) (8210637406732603/1000000000000000000000000) where
  r0 := (8064792721/12500000000000000)
  k0 := (759469535535113/200000000000000000)
  k6 := (11832096461853047/1000000000000000000)
  q := (81832145273113792419/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13393]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13393]

theorem width_13394 : mW 13394 = 278090421977262 := by
  have hu : mW 13394 ≤ 278090421977262 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13394 ≤ 278090421977261 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13394 : RowArithmetic 13394 (228868599900575910877/200000000000000000000000) (308262250410406729024741/500000000000000000000000) (6567230896351/800000000000000000000) where
  r0 := (645111164651/1000000000000000000)
  k0 := (1898567521182079/500000000000000000)
  k6 := (11831654759698461/1000000000000000000)
  q := (16367040050051811369/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13394]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13394]

theorem width_13395 : mW 13395 = 278163096855224 := by
  have hu : mW 13395 ≤ 278163096855224 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13395 ≤ 278163096855223 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13395 : RowArithmetic 13395 (1144306533426698216609/1000000000000000000000000) (308256036661723464803329/500000000000000000000000) (4103720134600373/500000000000000000000000) where
  r0 := (161259731277/250000000000000000)
  k0 := (3796922434836377/1000000000000000000)
  k6 := (473248524280301/40000000000000000)
  q := (40919127556681850643/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13395]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13395]

theorem width_13396 : mW 13396 = 278235785298260 := by
  have hu : mW 13396 ≤ 278235785298260 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13396 ≤ 278235785298259 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13396 : RowArithmetic 13396 (114427007648443628413/100000000000000000000000) (61649964769562337075921/100000000000000000000000) (512865147054161/62500000000000000000000) where
  r0 := (128993339809/200000000000000000)
  k0 := (3796709855079231/1000000000000000000)
  k6 := (11830771503771009/1000000000000000000)
  q := (163682619724880992021/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13396]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13396]

theorem width_13397 : mW 13397 = 278308487307887 := by
  have hu : mW 13397 ≤ 278308487307887 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13397 ≤ 278308487307886 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13397 : RowArithmetic 13397 (2288467257346202259/2000000000000000000000) (616487223936893723097781/1000000000000000000000000) (8204244871284409/1000000000000000000000000) where
  r0 := (644894486461/1000000000000000000)
  k0 := (94912432577361/25000000000000000)
  k6 := (11830329949979683/1000000000000000000)
  q := (81844364497502208903/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13397]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13397]

theorem width_13398 : mW 13398 = 278381202885625 := by
  have hu : mW 13398 ≤ 278381202885625 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13398 ≤ 278381202885624 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13398 : RowArithmetic 13398 (1144197189989699108773/1000000000000000000000000) (308237401023404517671787/500000000000000000000000) (8202647824302393/1000000000000000000000000) where
  r0 := (644822287351/1000000000000000000)
  k0 := (75925695577439/20000000000000000)
  k6 := (11829888445624321/1000000000000000000)
  q := (163694838037123210931/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13398]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13398]

theorem width_13399 : mW 13399 = 278453932032994 := by
  have hu : mW 13399 ≤ 278453932032994 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13399 ≤ 278453932032993 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13399 : RowArithmetic 13399 (1144160760431237833849/1000000000000000000000000) (308231191012460275684803/500000000000000000000000) (8201051211768743/1000000000000000000000000) where
  r0 := (644750101711/1000000000000000000)
  k0 := (3796072282404651/1000000000000000000)
  k6 := (11829446990695699/1000000000000000000)
  q := (40925236712815724409/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13399]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13399]

theorem width_13400 : mW 13400 = 278526674751512 := by
  have hu : mW 13400 ≤ 278526674751512 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13400 ≤ 278526674751511 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13400 : RowArithmetic 13400 (1144124339994727683187/1000000000000000000000000) (308224981935389794370489/500000000000000000000000) (4099727516765899/500000000000000000000000) where
  r0 := (644677929539/1000000000000000000)
  k0 := (1897929906845657/500000000000000000)
  k6 := (2957251396296149/250000000000000000)
  q := (818535277187244997/5000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13400]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13400]

theorem width_13401 : mW 13401 = 278599431042699 := by
  have hu : mW 13401 ≤ 278599431042699 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13401 ≤ 278599431042698 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13401 : RowArithmetic 13401 (1144087928677178776363/1000000000000000000000000) (616437547583937663091697/1000000000000000000000000) (256183102794997/31250000000000000000000) where
  r0 := (64460577083/100000000000000000)
  k0 := (3795647372721879/1000000000000000000)
  k6 := (184821316079403/15625000000000000)
  q := (163713163795707032937/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13401]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13401]

theorem width_13402 : mW 13402 = 278672200908074 := by
  have hu : mW 13402 ≤ 278672200908074 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13402 ≤ 278672200908073 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13402 : RowArithmetic 13402 (572025763237801620901/500000000000000000000000) (77053141645493294108123/125000000000000000000000) (128066624677211/15625000000000000000000) where
  r0 := (322266812791/500000000000000000)
  k0 := (3795434959495117/1000000000000000000)
  k6 := (11828122922378071/1000000000000000000)
  q := (81859635963031255103/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13402]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13402]

theorem width_13403 : mW 13403 = 278744984349157 := by
  have hu : mW 13403 ≤ 278744984349157 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13403 ≤ 278744984349156 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13403 : RowArithmetic 13403 (1144015133387013705031/1000000000000000000000000) (123282544122071514160457/200000000000000000000000) (8194669103085077/1000000000000000000000000) where
  r0 := (64446149379/100000000000000000)
  k0 := (948805643500241/250000000000000000)
  k6 := (11827681665064217/1000000000000000000)
  q := (81862689914270469201/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13403]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13403]

theorem width_13404 : mW 13404 = 278817781367466 := by
  have hu : mW 13404 ≤ 278817781367466 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13404 ≤ 278817781367465 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13404 : RowArithmetic 13404 (228795749881685110559/200000000000000000000000) (616400309922723220965311/1000000000000000000000000) (2048268665129807/250000000000000000000000) where
  r0 := (644389375451/1000000000000000000)
  k0 := (3795010216235241/1000000000000000000)
  k6 := (591362022856551/50000000000000000)
  q := (32746297500633563993/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13404]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13404]

theorem width_13405 : mW 13405 = 278890591964522 := by
  have hu : mW 13405 ≤ 278890591964522 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13405 ≤ 278890591964521 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13405 : RowArithmetic 13405 (1143942374536853158821/1000000000000000000000000) (123277580220119062617613/200000000000000000000000) (409574032574627/50000000000000000000000) where
  r0 := (322158635281/500000000000000000)
  k0 := (379479788619377/100000000000000000)
  k6 := (1182679929856927/100000000000000000)
  q := (8186879747498432629/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13405]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13405]

theorem width_13406 : mW 13406 = 278963416141845 := by
  have hu : mW 13406 ≤ 278963416141845 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13406 ≤ 278963416141844 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13406 : RowArithmetic 13406 (285976502192328225743/250000000000000000000000) (616375494143526151590011/1000000000000000000000000) (1023735884481711/125000000000000000000000) where
  r0 := (8053064739/12500000000000000)
  k0 := (3794585583872369/1000000000000000000)
  k6 := (11826358189369759/1000000000000000000)
  q := (163743702168968929173/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13406]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13406]

theorem width_13407 : mW 13407 = 279036253900953 := by
  have hu : mW 13407 ≤ 279036253900953 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13407 ≤ 279036253900952 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13407 : RowArithmetic 13407 (114386965210282392233/100000000000000000000000) (616363089051068133758933/1000000000000000000000000) (4094146966725739/500000000000000000000000) where
  r0 := (644173101119/1000000000000000000)
  k0 := (3794373309258019/1000000000000000000)
  k6 := (11825917129523283/1000000000000000000)
  q := (511718153625606681/3125000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13407]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13407]

theorem width_13408 : mW 13408 = 279109105243366 := by
  have hu : mW 13408 ≤ 279109105243366 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13408 ≤ 279109105243365 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13408 : RowArithmetic 13408 (571916652267202547477/500000000000000000000000) (308175342911386883689889/500000000000000000000000) (4093350612067359/500000000000000000000000) where
  r0 := (322050518279/500000000000000000)
  k0 := (948540265588107/250000000000000000)
  k6 := (73909225743879/6250000000000000)
  q := (511737237261468007/3125000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13408]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13408]

theorem width_13409 : mW 13409 = 279181970170605 := by
  have hu : mW 13409 ≤ 279181970170605 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13409 ≤ 279181970170604 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13409 : RowArithmetic 13409 (114379696606107579523/100000000000000000000000) (61633828445819573511843/100000000000000000000000) (1637021789550451/200000000000000000000000) where
  r0 := (644028985433/1000000000000000000)
  k0 := (1896974421574231/500000000000000000)
  k6 := (11825035157852629/1000000000000000000)
  q := (81881011229710640403/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13409]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13409]

theorem width_13410 : mW 13410 = 279254848684188 := by
  have hu : mW 13410 ≤ 279254848684188 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13410 ≤ 279254848684187 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13410 : RowArithmetic 13410 (1143760636679858904493/1000000000000000000000000) (24653035398275474173313/40000000000000000000000) (8183517104153091/1000000000000000000000000) where
  r0 := (32197847387/50000000000000000)
  k0 := (948434162909747/250000000000000000)
  k6 := (11824594246010053/1000000000000000000)
  q := (32753625753494833507/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13410]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13410]

theorem width_13411 : mW 13411 = 279327740785637 := by
  have hu : mW 13411 ≤ 279327740785637 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13411 ≤ 279327740785636 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13411 : RowArithmetic 13411 (571862158193887770411/500000000000000000000000) (154078371829600029356771/250000000000000000000000) (8181925693186173/1000000000000000000000000) where
  r0 := (25755396939/40000000000000000)
  k0 := (3793524487816871/1000000000000000000)
  k6 := (11824153383483717/1000000000000000000)
  q := (409435587119634729/2500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13411]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13411]

theorem width_13412 : mW 13412 = 279400646476470 := by
  have hu : mW 13412 ≤ 279400646476470 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13412 ≤ 279400646476469 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13412 : RowArithmetic 13412 (285922001295462769751/250000000000000000000000) (154075272885572152069087/250000000000000000000000) (2045083678675159/250000000000000000000000) where
  r0 := (128762582527/200000000000000000)
  k0 := (1896656175838959/500000000000000000)
  k6 := (11823712570264429/1000000000000000000)
  q := (163780340700585917423/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13412]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13412]

theorem width_13413 : mW 13413 = 279473565758209 := by
  have hu : mW 13413 ≤ 279473565758209 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13413 ≤ 279473565758208 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13413 : RowArithmetic 13413 (1143651703059109131837/1000000000000000000000000) (616288697628105625081707/1000000000000000000000000) (8178744168545561/1000000000000000000000000) where
  r0 := (643740915217/1000000000000000000)
  k0 := (1896550121608967/500000000000000000)
  k6 := (11823271806342997/1000000000000000000)
  q := (4094661158142392617/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13413]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13413]

theorem width_13414 : mW 13414 = 279546498632372 := by
  have hu : mW 13414 ≤ 279546498632372 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13414 ≤ 279546498632371 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13414 : RowArithmetic 13414 (571807705008288782433/500000000000000000000000) (308138152787702278314469/500000000000000000000000) (8177154054570211/1000000000000000000000000) where
  r0 := (643668931217/1000000000000000000)
  k0 := (189644408121489/50000000000000000)
  k6 := (5911415545855117/500000000000000000)
  q := (10237034482700544269/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13414]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13414]

theorem width_13415 : mW 13415 = 279619445100480 := by
  have hu : mW 13415 ≤ 279619445100480 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13415 ≤ 279619445100479 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13415 : RowArithmetic 13415 (1143579126051283233693/1000000000000000000000000) (616263915383738973855443/1000000000000000000000000) (817556437262383/100000000000000000000000) where
  r0 := (80449620079/125000000000000000)
  k0 := (3792676109309257/1000000000000000000)
  k6 := (5911195213178477/500000000000000000)
  q := (81899328446575189241/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13415]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13415]

theorem width_13416 : mW 13416 = 279692405164053 := by
  have hu : mW 13416 ≤ 279692405164053 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13416 ≤ 279692405164052 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13416 : RowArithmetic 13416 (285885712790063747509/250000000000000000000000) (38515720440791413383733/62500000000000000000000) (1634795024511151/200000000000000000000000) where
  r0 := (643525003457/1000000000000000000)
  k0 := (3792464083846273/1000000000000000000)
  k6 := (472877992410959/40000000000000000)
  q := (81902380917773080329/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13416]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13416]

theorem width_13417 : mW 13417 = 279765378824611 := by
  have hu : mW 13417 ≤ 279765378824611 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13417 ≤ 279765378824610 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13417 : RowArithmetic 13417 (228701317068104585857/200000000000000000000000) (123247828116345857666131/200000000000000000000000) (2043096576053847/250000000000000000000000) where
  r0 := (64345305969/100000000000000000)
  k0 := (1896126043019787/500000000000000000)
  k6 := (2364301848690423/200000000000000000)
  q := (32762173310084299107/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13417]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13417]

theorem width_13418 : mW 13418 = 279838366083675 := by
  have hu : mW 13418 ≤ 279838366083675 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13418 ≤ 279838366083674 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13418 : RowArithmetic 13418 (35733447768409926251/31250000000000000000000) (154056688992623245481981/250000000000000000000000) (817079791745217/100000000000000000000000) where
  r0 := (40211320583/62500000000000000)
  k0 := (1896020057942479/500000000000000000)
  k6 := (2955267181470549/250000000000000000)
  q := (40954242759450454769/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13418]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13418]

theorem width_13419 : mW 13419 = 279911366942765 := by
  have hu : mW 13419 ≤ 279911366942765 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13419 ≤ 279911366942764 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13419 : RowArithmetic 13419 (228686816180614340797/200000000000000000000000) (616214373218507876977289/1000000000000000000000000) (2042302490528909/250000000000000000000000) where
  r0 := (321654606183/500000000000000000)
  k0 := (151673126934893/40000000000000000)
  k6 := (5910314128777521/500000000000000000)
  q := (32764615059542512501/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13419]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13419]

theorem width_13420 : mW 13420 = 279984381403401 := by
  have hu : mW 13420 ≤ 279984381403401 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13420 ≤ 279984381403400 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13420 : RowArithmetic 13420 (1143397842279418944511/1000000000000000000000000) (24648079693013131418913/40000000000000000000000) (4083811219027693/500000000000000000000000) where
  r0 := (643237308801/1000000000000000000)
  k0 := (379161625849747/100000000000000000)
  k6 := (295504695961537/25000000000000000)
  q := (40957294832544788077/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13420]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13420]

theorem width_13421 : mW 13421 = 280057409467103 := by
  have hu : mW 13421 ≤ 280057409467103 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13421 ≤ 280057409467102 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13421 : RowArithmetic 13421 (1143361612715194425967/1000000000000000000000000) (123237922658101718387791/200000000000000000000000) (1633207069024217/200000000000000000000000) where
  r0 := (643165418629/1000000000000000000)
  k0 := (3791404371253237/1000000000000000000)
  k6 := (11819747468592339/1000000000000000000)
  q := (81917641567613505117/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13421]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13421]

theorem width_13422 : mW 13422 = 280130451135393 := by
  have hu : mW 13422 ≤ 280130451135393 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13422 ≤ 280130451135392 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13422 : RowArithmetic 13422 (285831348051858239007/250000000000000000000000) (61617723611360337310337/100000000000000000000000) (1020556085395301/125000000000000000000000) where
  r0 := (80386692731/125000000000000000)
  k0 := (947798127909591/250000000000000000)
  k6 := (11819307147938449/1000000000000000000)
  q := (163841386712881553297/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13422]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13422]

theorem width_13423 : mW 13423 = 280203506409791 := by
  have hu : mW 13423 ≤ 280203506409791 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13423 ≤ 280203506409790 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13423 : RowArithmetic 13423 (45731567230126883239/40000000000000000000000) (123232972158833490118669/200000000000000000000000) (163257249040583/20000000000000000000000) where
  r0 := (643021678453/1000000000000000000)
  k0 := (3790980679642743/1000000000000000000)
  k6 := (2954716719122661/250000000000000000)
  q := (10240468128948012111/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13423]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13423]

theorem width_13424 : mW 13424 = 280276575291817 := by
  have hu : mW 13424 ≤ 280276575291817 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13424 ≤ 280276575291816 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13424 : RowArithmetic 13424 (571626489174725293033/500000000000000000000000) (616152487331755622386451/1000000000000000000000000) (1020159581446397/125000000000000000000000) where
  r0 := (321474914221/500000000000000000)
  k0 := (379076887526511/100000000000000000)
  k6 := (11818426654239761/1000000000000000000)
  q := (8192679659305616961/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13424]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13424]

theorem width_13425 : mW 13425 = 280349657782992 := by
  have hu : mW 13425 ≤ 280349657782992 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13425 ≤ 280349657782991 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13425 : RowArithmetic 13425 (228643356998661549469/200000000000000000000000) (24645604629036915500791/40000000000000000000000) (509980705102399/62500000000000000000000) where
  r0 := (64287799181/100000000000000000)
  k0 := (473819637311919/125000000000000000)
  k6 := (11817986481176637/1000000000000000000)
  q := (81929848040869696221/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13425]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13425]

theorem width_13426 : mW 13426 = 280422753884836 := by
  have hu : mW 13426 ≤ 280422753884836 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13426 ≤ 280422753884835 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13426 : RowArithmetic 13426 (1143180600681784827001/1000000000000000000000000) (616127745976224505160317/1000000000000000000000000) (31867602898753/3906250000000000000000) where
  r0 := (321403084277/500000000000000000)
  k0 := (1895172674664627/500000000000000000)
  k6 := (5908773178646057/500000000000000000)
  q := (20483224843759343941/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13426]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13426]

theorem width_13427 : mW 13427 = 280495863598871 := by
  have hu : mW 13427 ≤ 280495863598871 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13427 ≤ 280495863598870 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13427 : RowArithmetic 13427 (571572212705961415219/500000000000000000000000) (616115378082215777938983/1000000000000000000000000) (8156521832748329/1000000000000000000000000) where
  r0 := (642734358671/1000000000000000000)
  k0 := (947533406940649/250000000000000000)
  k6 := (5908553141288517/500000000000000000)
  q := (81935950595571904917/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13427]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13427]

theorem width_13428 : mW 13428 = 280568986926618 := by
  have hu : mW 13428 ≤ 280568986926618 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13428 ≤ 280568986926617 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13428 : RowArithmetic 13428 (1143108259180764748519/1000000000000000000000000) (616103012043452078275429/1000000000000000000000000) (4077468876745581/500000000000000000000000) where
  r0 := (642662562157/1000000000000000000)
  k0 := (236870120861763/62500000000000000)
  k6 := (2954166564255561/250000000000000000)
  q := (163878003404971955987/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13428]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13428]

theorem width_13429 : mW 13429 = 280642123869596 := by
  have hu : mW 13429 ≤ 280642123869596 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13429 ≤ 280642123869595 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13429 : RowArithmetic 13429 (1143072101985356301497/1000000000000000000000000) (616090647859489104776059/1000000000000000000000000) (4076677052079743/500000000000000000000000) where
  r0 := (642590779009/1000000000000000000)
  k0 := (378971026740187/100000000000000000)
  k6 := (11816226280618591/1000000000000000000)
  q := (2560689146743508967/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13429]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13429]

theorem width_13430 : mW 13430 = 280715274429328 := by
  have hu : mW 13430 ≤ 280715274429328 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13430 ≤ 280715274429327 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13430 : RowArithmetic 13430 (7143974711392134123/6250000000000000000000) (616078285529882538187103/1000000000000000000000000) (8151770884603469/1000000000000000000000000) where
  r0 := (642519009223/1000000000000000000)
  k0 := (473687328574551/125000000000000000)
  k6 := (472631454134277/40000000000000000)
  q := (163890207151007042713/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13430]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13430]

theorem width_13431 : mW 13431 = 280788438607334 := by
  have hu : mW 13431 ≤ 280788438607334 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13431 ≤ 280788438607333 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13431 : RowArithmetic 13431 (1142999814689967668313/1000000000000000000000000) (24642637002167532753841/40000000000000000000000) (8150188094673433/1000000000000000000000000) where
  r0 := (160611813199/250000000000000000)
  k0 := (757857403473519/200000000000000000)
  k6 := (11815346475228099/1000000000000000000)
  q := (163896308683264736913/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13431]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13431]

theorem width_13432 : mW 13432 = 280861616405135 := by
  have hu : mW 13432 ≤ 280861616405135 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13432 ≤ 280861616405134 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13432 : RowArithmetic 13432 (1142963684584082861019/1000000000000000000000000) (38503347901997657415663/62500000000000000000000) (8148605734219733/1000000000000000000000000) where
  r0 := (160593877431/250000000000000000)
  k0 := (757815086741651/200000000000000000)
  k6 := (11814906646222969/1000000000000000000)
  q := (163902409988383026217/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13432]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13432]

theorem width_13433 : mW 13433 = 280934807824252 := by
  have hu : mW 13433 ≤ 280934807824252 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13433 ≤ 280934807824251 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13433 : RowArithmetic 13433 (1142927563502136205689/1000000000000000000000000) (616041209662761254509397/1000000000000000000000000) (1018377975386599/125000000000000000000000) where
  r0 := (160575945001/250000000000000000)
  k0 := (3788863877614159/1000000000000000000)
  k6 := (11814466866332391/1000000000000000000)
  q := (16390851106638727563/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13433]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13433]

theorem width_13434 : mW 13434 = 281008012866207 := by
  have hu : mW 13434 ≤ 281008012866207 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13434 ≤ 281008012866206 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13434 : RowArithmetic 13434 (1142891451441177359203/1000000000000000000000000) (616028854746140931735647/1000000000000000000000000) (2036360575285767/250000000000000000000000) where
  r0 := (40139503977/62500000000000000)
  k0 := (1894326174539063/500000000000000000)
  k6 := (5907013567773613/500000000000000000)
  q := (163914611917302845439/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13434]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13434]

theorem width_13435 : mW 13435 = 281081231532520 := by
  have hu : mW 13435 ≤ 281081231532520 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13435 ≤ 281081231532519 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13435 : RowArithmetic 13435 (228571069679651740249/200000000000000000000000) (308008250840829007643271/500000000000000000000000) (4071930614110571/500000000000000000000000) where
  r0 := (128432072121/200000000000000000)
  k0 := (3788440848095923/1000000000000000000)
  k6 := (369174607933073/31250000000000000)
  q := (163920712541155091211/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13435]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13435]

theorem width_13436 : mW 13436 = 281154463824714 := by
  have hu : mW 13436 ≤ 281154463824714 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13436 ≤ 281154463824713 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13436 : RowArithmetic 13436 (57140962718521580529/50000000000000000000000) (24640166018754763467223/40000000000000000000000) (325691223367103/40000000000000000000000) where
  r0 := (642088670919/1000000000000000000)
  k0 := (947057343665091/250000000000000000)
  k6 := (2362629564251317/200000000000000000)
  q := (163926812937969363793/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13436]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13436]

theorem width_13437 : mW 13437 = 281227709744308 := by
  have hu : mW 13437 ≤ 281227709744308 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13437 ≤ 281227709744307 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13437 : RowArithmetic 13437 (142847896169343959341/125000000000000000000000) (615991801107330939682129/1000000000000000000000000) (4070350184431553/500000000000000000000000) where
  r0 := (642016994571/1000000000000000000)
  k0 := (1894008964383607/500000000000000000)
  k6 := (295317705943321/25000000000000000)
  q := (163932913107771009317/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13437]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13437]

theorem width_13438 : mW 13438 = 281300969292826 := by
  have hu : mW 13438 ≤ 281300969292826 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13438 ≤ 281300969292825 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13438 : RowArithmetic 13438 (1142747093348271992973/1000000000000000000000000) (307989726798300263014417/500000000000000000000000) (8139120582128397/1000000000000000000000000) where
  r0 := (320972665779/500000000000000000)
  k0 := (1893903255206117/500000000000000000)
  k6 := (2953067175819493/250000000000000000)
  q := (163939013050585369199/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13438]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13438]

theorem width_13439 : mW 13439 = 281374242471788 := by
  have hu : mW 13439 ≤ 281374242471788 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13439 ≤ 281374242471787 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13439 : RowArithmetic 13439 (114271102634804987073/100000000000000000000000) (615967107936234885263573/1000000000000000000000000) (813754122382429/100000000000000000000000) where
  r0 := (1026997891/1600000000000000)
  k0 := (3787595119585283/1000000000000000000)
  k6 := (11811829217882851/1000000000000000000)
  q := (81972556383218890071/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13439]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13439]

theorem width_13440 : mW 13440 = 281447529282715 := by
  have hu : mW 13440 ≤ 281447529282715 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13440 ≤ 281447529282714 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13440 : RowArithmetic 13440 (1142674968351143099061/1000000000000000000000000) (615954764125791205942709/1000000000000000000000000) (8135962293801661/1000000000000000000000000) where
  r0 := (8022525569/12500000000000000)
  k0 := (378738375628507/100000000000000000)
  k6 := (11811389781538351/1000000000000000000)
  q := (40987803063838393533/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13440]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13440]

theorem width_13441 : mW 13441 = 281520829727130 := by
  have hu : mW 13441 ≤ 281520829727130 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13441 ≤ 281520829727129 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13441 : RowArithmetic 13441 (1142638919354609213273/1000000000000000000000000) (30797121108241345254939/50000000000000000000000) (4067191895955699/500000000000000000000000) where
  r0 := (641730422489/1000000000000000000)
  k0 := (9467931051261/2500000000000000)
  k6 := (236219007884707/20000000000000000)
  q := (163957311517358078447/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13441]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13441]

theorem width_13442 : mW 13442 = 281594143806553 := by
  have hu : mW 13442 ≤ 281594143806553 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13442 ≤ 281594143806552 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13442 : RowArithmetic 13442 (1142602879355509205627/1000000000000000000000000) (153982520513224853115027/250000000000000000000000) (1626561143600907/200000000000000000000000) where
  r0 := (320829406389/500000000000000000)
  k0 := (3786961112236077/1000000000000000000)
  k6 := (5905255527982363/500000000000000000)
  q := (163963410552476615651/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13442]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13442]

theorem width_13443 : mW 13443 = 281667471522507 := by
  have hu : mW 13443 ≤ 281667471522507 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13443 ≤ 281667471522506 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13443 : RowArithmetic 13443 (1142566848350903069593/1000000000000000000000000) (307958871894783176518501/500000000000000000000000) (8131228071932089/1000000000000000000000000) where
  r0 := (2447461/3814697265625)
  k0 := (3786749831475853/1000000000000000000)
  k6 := (11810071766717361/1000000000000000000)
  q := (81984754680367251801/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13443]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13443]

theorem width_13444 : mW 13444 = 281740812876513 := by
  have hu : mW 13444 ≤ 281740812876513 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13444 ≤ 281740812876512 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13444 : RowArithmetic 13444 (285632706584463377737/250000000000000000000000) (615905407374385562583463/1000000000000000000000000) (2032412713386299/250000000000000000000000) where
  r0 := (80189454163/125000000000000000)
  k0 := (94663464455487/25000000000000000)
  k6 := (11809632526484137/1000000000000000000)
  q := (163975607942157055447/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13444]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13444]

theorem width_13445 : mW 13445 = 281814167870094 := by
  have hu : mW 13445 ≤ 281814167870094 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13445 ≤ 281814167870093 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13445 : RowArithmetic 13445 (1142494813313422979641/1000000000000000000000000) (615893072806914994508083/1000000000000000000000000) (4064037031347501/500000000000000000000000) where
  r0 := (320722031767/500000000000000000)
  k0 := (946581838114939/250000000000000000)
  k6 := (11809193335255941/1000000000000000000)
  q := (81990853148384789813/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13445]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13445]

theorem width_13446 : mW 13446 = 281887536504770 := by
  have hu : mW 13446 ≤ 281887536504770 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13446 ≤ 281887536504769 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13446 : RowArithmetic 13446 (1142458809274677376057/1000000000000000000000000) (615880740086712696845821/1000000000000000000000000) (4063248849616401/500000000000000000000000) where
  r0 := (641372507071/1000000000000000000)
  k0 := (3786116154192427/1000000000000000000)
  k6 := (5904377096511831/500000000000000000)
  q := (40996951106149344969/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13446]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13446]

theorem width_13447 : mW 13447 = 281960918782064 := by
  have hu : mW 13447 ≤ 281960918782064 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13447 ≤ 281960918782063 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13447 : RowArithmetic 13447 (114242281421868160301/100000000000000000000000) (76983551151667110780811/125000000000000000000000) (8124921763009871/1000000000000000000000000) where
  r0 := (641300963911/1000000000000000000)
  k0 := (236619061463143/62500000000000000)
  k6 := (1180831509977819/100000000000000000)
  q := (6559756093026630209/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13447]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13447]

theorem width_13448 : mW 13448 = 282034314703498 := by
  have hu : mW 13448 ≤ 282034314703498 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13448 ≤ 282034314703497 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13448 : RowArithmetic 13448 (1142386828142502530297/1000000000000000000000000) (307928040093172959926041/500000000000000000000000) (8123346253877577/1000000000000000000000000) where
  r0 := (12824588681/20000000000000000)
  k0 := (3785693840106131/1000000000000000000)
  k6 := (5903938027755209/500000000000000000)
  q := 164
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13448]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13448]

theorem width_13449 : mW 13449 = 282107724270594 := by
  have hu : mW 13449 ≤ 282107724270594 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13449 ≤ 282107724270593 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13449 : RowArithmetic 13449 (71396928190200515791/62500000000000000000000) (615843753005298364617199/1000000000000000000000000) (8121771171687353/1000000000000000000000000) where
  r0 := (320578958743/500000000000000000)
  k0 := (3785482724278649/1000000000000000000)
  k6 := (5903718530105621/500000000000000000)
  q := (41001524361906350957/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13449]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13449]

theorem width_13450 : mW 13450 = 282181147484874 := by
  have hu : mW 13450 ≤ 282181147484874 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13450 ≤ 282181147484873 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13450 : RowArithmetic 13450 (571157441458934044553/500000000000000000000000) (615831427669752774019463/1000000000000000000000000) (1015024564536337/125000000000000000000000) where
  r0 := (128217282843/200000000000000000)
  k0 := (3785271635920631/1000000000000000000)
  k6 := (11806998113871559/1000000000000000000)
  q := (164012194668567251631/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13450]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13450]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 13376 then ⟨(572500477097588844439/500000000000000000000000), (1233497031956229005319/2000000000000000000000), (8237883484829073/1000000000000000000000000)⟩ else
  if n = 13377 then ⟨(1144964323195037641119/1000000000000000000000000), (123347210950402117242727/200000000000000000000000), (8236277279274017/1000000000000000000000000)⟩ else
  if n = 13378 then ⟨(1144927701382920826327/1000000000000000000000000), (61672359540355861317121/100000000000000000000000), (4117335755683979/500000000000000000000000)⟩ else
  if n = 13379 then ⟨(286222772188952981643/250000000000000000000000), (616711137932306848404291/1000000000000000000000000), (1646613236191573/200000000000000000000000)⟩ else
  if n = 13380 then ⟨(1144854485310696126457/1000000000000000000000000), (308349341168901837936509/500000000000000000000000), (1028932660986343/125000000000000000000000)⟩ else
  if n = 13381 then ⟨(572408945522279557051/500000000000000000000000), (616686228619597642825227/1000000000000000000000000), (8229856832013639/1000000000000000000000000)⟩ else
  if n = 13382 then ⟨(1144781305954389367047/1000000000000000000000000), (308336888388618726172089/500000000000000000000000), (8228252813173719/1000000000000000000000000)⟩ else
  if n = 13383 then ⟨(286186182509293585421/250000000000000000000000), (123332265362054377901917/200000000000000000000000), (8226649231218133/1000000000000000000000000)⟩ else
  if n = 13384 then ⟨(14308852041123813043/12500000000000000000000), (616648878718249990224493/1000000000000000000000000), (1028130760749273/125000000000000000000000)⟩ else
  if n = 13385 then ⟨(1144671605709572217861/1000000000000000000000000), (308318216250360426186657/500000000000000000000000), (128491302771081/15625000000000000000000)⟩ else
  if n = 13386 then ⟨(35769845540411519819/31250000000000000000000), (7707799851965421970249/12500000000000000000000), (8221841105130539/1000000000000000000000000)⟩ else
  if n = 13387 then ⟨(114459851803768756313/100000000000000000000000), (616611545687338157135921/1000000000000000000000000), (256882477162053/31250000000000000000000)⟩ else
  if n = 13388 then ⟨(1144561987940124296961/1000000000000000000000000), (616599105090583638630597/1000000000000000000000000), (1643727573872439/200000000000000000000000)⟩ else
  if n = 13389 then ⟨(572262733498737314361/500000000000000000000000), (123317333273303968292303/200000000000000000000000), (4108518452753807/500000000000000000000000)⟩ else
  if n = 13390 then ⟨(1144488955206736371087/1000000000000000000000000), (154143557378674185554169/250000000000000000000000), (8215436377469629/1000000000000000000000000)⟩ else
  if n = 13391 then ⟨(1144452452564907078051/1000000000000000000000000), (616561794534664287408089/1000000000000000000000000), (102672953563699/12500000000000000000000)⟩ else
  if n = 13392 then ⟨(1144415959068987080893/1000000000000000000000000), (616549361425972708200139/1000000000000000000000000), (8212236628234297/1000000000000000000000000)⟩ else
  if n = 13393 then ⟨(572189737357988605087/500000000000000000000000), (123307386037634452697437/200000000000000000000000), (8210637406732603/1000000000000000000000000)⟩ else
  if n = 13394 then ⟨(228868599900575910877/200000000000000000000000), (308262250410406729024741/500000000000000000000000), (6567230896351/800000000000000000000)⟩ else
  if n = 13395 then ⟨(1144306533426698216609/1000000000000000000000000), (308256036661723464803329/500000000000000000000000), (4103720134600373/500000000000000000000000)⟩ else
  if n = 13396 then ⟨(114427007648443628413/100000000000000000000000), (61649964769562337075921/100000000000000000000000), (512865147054161/62500000000000000000000)⟩ else
  if n = 13397 then ⟨(2288467257346202259/2000000000000000000000), (616487223936893723097781/1000000000000000000000000), (8204244871284409/1000000000000000000000000)⟩ else
  if n = 13398 then ⟨(1144197189989699108773/1000000000000000000000000), (308237401023404517671787/500000000000000000000000), (8202647824302393/1000000000000000000000000)⟩ else
  if n = 13399 then ⟨(1144160760431237833849/1000000000000000000000000), (308231191012460275684803/500000000000000000000000), (8201051211768743/1000000000000000000000000)⟩ else
  if n = 13400 then ⟨(1144124339994727683187/1000000000000000000000000), (308224981935389794370489/500000000000000000000000), (4099727516765899/500000000000000000000000)⟩ else
  if n = 13401 then ⟨(1144087928677178776363/1000000000000000000000000), (616437547583937663091697/1000000000000000000000000), (256183102794997/31250000000000000000000)⟩ else
  if n = 13402 then ⟨(572025763237801620901/500000000000000000000000), (77053141645493294108123/125000000000000000000000), (128066624677211/15625000000000000000000)⟩ else
  if n = 13403 then ⟨(1144015133387013705031/1000000000000000000000000), (123282544122071514160457/200000000000000000000000), (8194669103085077/1000000000000000000000000)⟩ else
  if n = 13404 then ⟨(228795749881685110559/200000000000000000000000), (616400309922723220965311/1000000000000000000000000), (2048268665129807/250000000000000000000000)⟩ else
  if n = 13405 then ⟨(1143942374536853158821/1000000000000000000000000), (123277580220119062617613/200000000000000000000000), (409574032574627/50000000000000000000000)⟩ else
  if n = 13406 then ⟨(285976502192328225743/250000000000000000000000), (616375494143526151590011/1000000000000000000000000), (1023735884481711/125000000000000000000000)⟩ else
  if n = 13407 then ⟨(114386965210282392233/100000000000000000000000), (616363089051068133758933/1000000000000000000000000), (4094146966725739/500000000000000000000000)⟩ else
  if n = 13408 then ⟨(571916652267202547477/500000000000000000000000), (308175342911386883689889/500000000000000000000000), (4093350612067359/500000000000000000000000)⟩ else
  if n = 13409 then ⟨(114379696606107579523/100000000000000000000000), (61633828445819573511843/100000000000000000000000), (1637021789550451/200000000000000000000000)⟩ else
  if n = 13410 then ⟨(1143760636679858904493/1000000000000000000000000), (24653035398275474173313/40000000000000000000000), (8183517104153091/1000000000000000000000000)⟩ else
  if n = 13411 then ⟨(571862158193887770411/500000000000000000000000), (154078371829600029356771/250000000000000000000000), (8181925693186173/1000000000000000000000000)⟩ else
  if n = 13412 then ⟨(285922001295462769751/250000000000000000000000), (154075272885572152069087/250000000000000000000000), (2045083678675159/250000000000000000000000)⟩ else
  if n = 13413 then ⟨(1143651703059109131837/1000000000000000000000000), (616288697628105625081707/1000000000000000000000000), (8178744168545561/1000000000000000000000000)⟩ else
  if n = 13414 then ⟨(571807705008288782433/500000000000000000000000), (308138152787702278314469/500000000000000000000000), (8177154054570211/1000000000000000000000000)⟩ else
  if n = 13415 then ⟨(1143579126051283233693/1000000000000000000000000), (616263915383738973855443/1000000000000000000000000), (817556437262383/100000000000000000000000)⟩ else
  if n = 13416 then ⟨(285885712790063747509/250000000000000000000000), (38515720440791413383733/62500000000000000000000), (1634795024511151/200000000000000000000000)⟩ else
  if n = 13417 then ⟨(228701317068104585857/200000000000000000000000), (123247828116345857666131/200000000000000000000000), (2043096576053847/250000000000000000000000)⟩ else
  if n = 13418 then ⟨(35733447768409926251/31250000000000000000000), (154056688992623245481981/250000000000000000000000), (817079791745217/100000000000000000000000)⟩ else
  if n = 13419 then ⟨(228686816180614340797/200000000000000000000000), (616214373218507876977289/1000000000000000000000000), (2042302490528909/250000000000000000000000)⟩ else
  if n = 13420 then ⟨(1143397842279418944511/1000000000000000000000000), (24648079693013131418913/40000000000000000000000), (4083811219027693/500000000000000000000000)⟩ else
  if n = 13421 then ⟨(1143361612715194425967/1000000000000000000000000), (123237922658101718387791/200000000000000000000000), (1633207069024217/200000000000000000000000)⟩ else
  if n = 13422 then ⟨(285831348051858239007/250000000000000000000000), (61617723611360337310337/100000000000000000000000), (1020556085395301/125000000000000000000000)⟩ else
  if n = 13423 then ⟨(45731567230126883239/40000000000000000000000), (123232972158833490118669/200000000000000000000000), (163257249040583/20000000000000000000000)⟩ else
  if n = 13424 then ⟨(571626489174725293033/500000000000000000000000), (616152487331755622386451/1000000000000000000000000), (1020159581446397/125000000000000000000000)⟩ else
  if n = 13425 then ⟨(228643356998661549469/200000000000000000000000), (24645604629036915500791/40000000000000000000000), (509980705102399/62500000000000000000000)⟩ else
  if n = 13426 then ⟨(1143180600681784827001/1000000000000000000000000), (616127745976224505160317/1000000000000000000000000), (31867602898753/3906250000000000000000)⟩ else
  if n = 13427 then ⟨(571572212705961415219/500000000000000000000000), (616115378082215777938983/1000000000000000000000000), (8156521832748329/1000000000000000000000000)⟩ else
  if n = 13428 then ⟨(1143108259180764748519/1000000000000000000000000), (616103012043452078275429/1000000000000000000000000), (4077468876745581/500000000000000000000000)⟩ else
  if n = 13429 then ⟨(1143072101985356301497/1000000000000000000000000), (616090647859489104776059/1000000000000000000000000), (4076677052079743/500000000000000000000000)⟩ else
  if n = 13430 then ⟨(7143974711392134123/6250000000000000000000), (616078285529882538187103/1000000000000000000000000), (8151770884603469/1000000000000000000000000)⟩ else
  if n = 13431 then ⟨(1142999814689967668313/1000000000000000000000000), (24642637002167532753841/40000000000000000000000), (8150188094673433/1000000000000000000000000)⟩ else
  if n = 13432 then ⟨(1142963684584082861019/1000000000000000000000000), (38503347901997657415663/62500000000000000000000), (8148605734219733/1000000000000000000000000)⟩ else
  if n = 13433 then ⟨(1142927563502136205689/1000000000000000000000000), (616041209662761254509397/1000000000000000000000000), (1018377975386599/125000000000000000000000)⟩ else
  if n = 13434 then ⟨(1142891451441177359203/1000000000000000000000000), (616028854746140931735647/1000000000000000000000000), (2036360575285767/250000000000000000000000)⟩ else
  if n = 13435 then ⟨(228571069679651740249/200000000000000000000000), (308008250840829007643271/500000000000000000000000), (4071930614110571/500000000000000000000000)⟩ else
  if n = 13436 then ⟨(57140962718521580529/50000000000000000000000), (24640166018754763467223/40000000000000000000000), (325691223367103/40000000000000000000000)⟩ else
  if n = 13437 then ⟨(142847896169343959341/125000000000000000000000), (615991801107330939682129/1000000000000000000000000), (4070350184431553/500000000000000000000000)⟩ else
  if n = 13438 then ⟨(1142747093348271992973/1000000000000000000000000), (307989726798300263014417/500000000000000000000000), (8139120582128397/1000000000000000000000000)⟩ else
  if n = 13439 then ⟨(114271102634804987073/100000000000000000000000), (615967107936234885263573/1000000000000000000000000), (813754122382429/100000000000000000000000)⟩ else
  if n = 13440 then ⟨(1142674968351143099061/1000000000000000000000000), (615954764125791205942709/1000000000000000000000000), (8135962293801661/1000000000000000000000000)⟩ else
  if n = 13441 then ⟨(1142638919354609213273/1000000000000000000000000), (30797121108241345254939/50000000000000000000000), (4067191895955699/500000000000000000000000)⟩ else
  if n = 13442 then ⟨(1142602879355509205627/1000000000000000000000000), (153982520513224853115027/250000000000000000000000), (1626561143600907/200000000000000000000000)⟩ else
  if n = 13443 then ⟨(1142566848350903069593/1000000000000000000000000), (307958871894783176518501/500000000000000000000000), (8131228071932089/1000000000000000000000000)⟩ else
  if n = 13444 then ⟨(285632706584463377737/250000000000000000000000), (615905407374385562583463/1000000000000000000000000), (2032412713386299/250000000000000000000000)⟩ else
  if n = 13445 then ⟨(1142494813313422979641/1000000000000000000000000), (615893072806914994508083/1000000000000000000000000), (4064037031347501/500000000000000000000000)⟩ else
  if n = 13446 then ⟨(1142458809274677376057/1000000000000000000000000), (615880740086712696845821/1000000000000000000000000), (4063248849616401/500000000000000000000000)⟩ else
  if n = 13447 then ⟨(114242281421868160301/100000000000000000000000), (76983551151667110780811/125000000000000000000000), (8124921763009871/1000000000000000000000000)⟩ else
  if n = 13448 then ⟨(1142386828142502530297/1000000000000000000000000), (307928040093172959926041/500000000000000000000000), (8123346253877577/1000000000000000000000000)⟩ else
  if n = 13449 then ⟨(71396928190200515791/62500000000000000000000), (615843753005298364617199/1000000000000000000000000), (8121771171687353/1000000000000000000000000)⟩ else
  ⟨(571157441458934044553/500000000000000000000000), (615831427669752774019463/1000000000000000000000000), (1015024564536337/125000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 13376 ≤ n) (hb : n ≤ 13450) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_13376
  · exact row_13377
  · exact row_13378
  · exact row_13379
  · exact row_13380
  · exact row_13381
  · exact row_13382
  · exact row_13383
  · exact row_13384
  · exact row_13385
  · exact row_13386
  · exact row_13387
  · exact row_13388
  · exact row_13389
  · exact row_13390
  · exact row_13391
  · exact row_13392
  · exact row_13393
  · exact row_13394
  · exact row_13395
  · exact row_13396
  · exact row_13397
  · exact row_13398
  · exact row_13399
  · exact row_13400
  · exact row_13401
  · exact row_13402
  · exact row_13403
  · exact row_13404
  · exact row_13405
  · exact row_13406
  · exact row_13407
  · exact row_13408
  · exact row_13409
  · exact row_13410
  · exact row_13411
  · exact row_13412
  · exact row_13413
  · exact row_13414
  · exact row_13415
  · exact row_13416
  · exact row_13417
  · exact row_13418
  · exact row_13419
  · exact row_13420
  · exact row_13421
  · exact row_13422
  · exact row_13423
  · exact row_13424
  · exact row_13425
  · exact row_13426
  · exact row_13427
  · exact row_13428
  · exact row_13429
  · exact row_13430
  · exact row_13431
  · exact row_13432
  · exact row_13433
  · exact row_13434
  · exact row_13435
  · exact row_13436
  · exact row_13437
  · exact row_13438
  · exact row_13439
  · exact row_13440
  · exact row_13441
  · exact row_13442
  · exact row_13443
  · exact row_13444
  · exact row_13445
  · exact row_13446
  · exact row_13447
  · exact row_13448
  · exact row_13449
  · exact row_13450

end BstLean.Part271.R3.Rows13376
