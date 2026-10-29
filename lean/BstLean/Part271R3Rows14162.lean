import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14162–14236. -/
namespace BstLean.Part271.R3.Rows14162
open Real BstLean.Part130 BstLean.Part227

theorem width_14162 : mW 14162 = 338015071529367 := by
  have hu : mW 14162 ≤ 338015071529367 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14162 ≤ 338015071529366 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14162 : RowArithmetic 14162 (1118818314912379507887/1000000000000000000000000) (60749904084261492123691/100000000000000000000000) (3549519010027327/500000000000000000000000) where
  r0 := (296676481159/500000000000000000)
  k0 := (1820812916516089/500000000000000000)
  k6 := (5753185077829/500000000000000)
  q := (168297355891291411579/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14162]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14162]

theorem width_14163 : mW 14163 = 338098616026998 := by
  have hu : mW 14163 ≤ 338098616026998 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14163 ≤ 338098616026997 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14163 : RowArithmetic 14163 (559394032624104361279/500000000000000000000000) (607487927175161454704551/1000000000000000000000000) (7097733377071309/1000000000000000000000000) where
  r0 := (118658024311/200000000000000000)
  k0 := (3641432989463661/1000000000000000000)
  k6 := (11505963936168167/1000000000000000000)
  q := (21037912206300320047/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14163]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14163]

theorem width_14164 : mW 14164 = 338182175272893 := by
  have hu : mW 14164 ≤ 338182175272893 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14164 ≤ 338182175272892 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14164 : RowArithmetic 14164 (559378911367919163447/500000000000000000000000) (303738407535826010927793/500000000000000000000000) (354821453460197/50000000000000000000000) where
  r0 := (593227291883/1000000000000000000)
  k0 := (1820620084860173/500000000000000000)
  k6 := (2876389439924667/250000000000000000)
  q := (84154619599876987383/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14164]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14164]

theorem width_14165 : mW 14165 = 338265749268616 := by
  have hu : mW 14165 ≤ 338265749268616 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14165 ≤ 338265749268615 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14165 : RowArithmetic 14165 (139840948421631741183/125000000000000000000000) (303732852265867463916679/500000000000000000000000) (7095125096341999/1000000000000000000000000) where
  r0 := (593164473299/1000000000000000000)
  k0 := (3641047373796811/1000000000000000000)
  k6 := (2876287906560477/250000000000000000)
  q := (21039397567420983549/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14165]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14165]

theorem width_14166 : mW 14166 = 338349338015728 := by
  have hu : mW 14166 ≤ 338349338015728 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14166 ≤ 338349338015727 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14166 : RowArithmetic 14166 (559348679578821828223/500000000000000000000000) (7593182444438233957377/12500000000000000000000) (141876429167501/20000000000000000000000) where
  r0 := (296550832901/500000000000000000)
  k0 := (364085460169377/100000000000000000)
  k6 := (1438093191973787/125000000000000000)
  q := (168321121669266450977/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14166]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14166]

theorem width_14167 : mW 14167 = 338432941515791 := by
  have hu : mW 14167 ≤ 338432941515791 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14167 ≤ 338432941515790 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14167 : RowArithmetic 14167 (1118667138087395962597/1000000000000000000000000) (607443488141271941881947/1000000000000000000000000) (7092518155192679/1000000000000000000000000) where
  r0 := (148259717347/250000000000000000)
  k0 := (364066185340273/100000000000000000)
  k6 := (2300867897667249/200000000000000000)
  q := (6733082503578877133/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14167]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14167]

theorem width_14168 : mW 14168 = 338516559770368 := by
  have hu : mW 14168 ≤ 338516559770368 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14168 ≤ 338516559770367 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14168 : RowArithmetic 14168 (111863692416009963193/100000000000000000000000) (121486476458004657037131/200000000000000000000000) (3545607593342249/500000000000000000000000) where
  r0 := (296488042027/500000000000000000)
  k0 := (455058641114783/125000000000000000)
  k6 := (2300786696774433/200000000000000000)
  q := (2104162541250081279/12500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14168]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14168]

theorem width_14169 : mW 14169 = 338600192781021 := by
  have hu : mW 14169 ≤ 338600192781021 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14169 ≤ 338600192781020 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14169 : RowArithmetic 14169 (69912919835846554381/62500000000000000000000) (607421278000961550033107/1000000000000000000000000) (3544956276370093/500000000000000000000000) where
  r0 := (296456654899/500000000000000000)
  k0 := (3640276428238013/1000000000000000000)
  k6 := (11503527522390473/1000000000000000000)
  q := (168338943800892370931/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14169]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14169]

theorem width_14170 : mW 14170 = 338683840549312 := by
  have hu : mW 14170 ≤ 338683840549312 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14170 ≤ 338683840549311 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14170 : RowArithmetic 14170 (1118576517725522757183/1000000000000000000000000) (607410175273735663187729/1000000000000000000000000) (1417722050649893/200000000000000000000000) where
  r0 := (592850546617/1000000000000000000)
  k0 := (3640083751356547/1000000000000000000)
  k6 := (2300624320776717/200000000000000000)
  q := (16834488409215172821/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14170]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14170]

theorem width_14171 : mW 14171 = 338767503076802 := by
  have hu : mW 14171 ≤ 338767503076802 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14171 ≤ 338767503076801 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14171 : RowArithmetic 14171 (34954572662932056021/31250000000000000000000) (151849768526998650939421/250000000000000000000000) (442956768006383/62500000000000000000000) where
  r0 := (592787794509/1000000000000000000)
  k0 := (1819945549135753/500000000000000000)
  k6 := (5751357864171959/500000000000000000)
  q := (16835082417380676429/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14171]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14171]

theorem width_14172 : mW 14172 = 338851180365056 := by
  have hu : mW 14172 ≤ 338851180365056 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14172 ≤ 338851180365055 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14172 : RowArithmetic 14172 (1118516139836245167977/1000000000000000000000000) (303693987251693751237781/500000000000000000000000) (1771501664296981/250000000000000000000000) where
  r0 := (59272505347/100000000000000000)
  k0 := (909924617243597/250000000000000000)
  k6 := (11502309895763893/1000000000000000000)
  q := (168356764045879665393/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14172]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14172]

theorem width_14173 : mW 14173 = 338934872415635 := by
  have hu : mW 14173 ≤ 338934872415635 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14173 ≤ 338934872415634 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14173 : RowArithmetic 14173 (1118485961590575130121/1000000000000000000000000) (151844219114890912955949/250000000000000000000000) (110698521256199/15625000000000000000000) where
  r0 := (592662323497/1000000000000000000)
  k0 := (3639505863459757/1000000000000000000)
  k6 := (11501904106135933/1000000000000000000)
  q := (168362703708392613827/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14173]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14173]

theorem width_14174 : mW 14174 = 339018579230102 := by
  have hu : mW 14174 ≤ 339018579230102 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14174 ≤ 339018579230101 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14174 : RowArithmetic 14174 (1118455790474609708419/1000000000000000000000000) (303682889988086150974823/500000000000000000000000) (442712774851153/62500000000000000000000) where
  r0 := (592599604589/1000000000000000000)
  k0 := (11372854005401/3125000000000000)
  k6 := (5750749179726231/500000000000000000)
  q := (84184321580683893993/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14174]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14174]

theorem width_14175 : mW 14175 = 339102300810019 := by
  have hu : mW 14175 ≤ 339102300810019 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14175 ≤ 339102300810018 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14175 : RowArithmetic 14175 (559212813243072174897/500000000000000000000000) (607354685052862941651399/1000000000000000000000000) (1770525942185753/250000000000000000000000) where
  r0 := (296268448371/500000000000000000)
  k0 := (227445045235723/62500000000000000)
  k6 := (718818290981619/62500000000000000)
  q := (10523411400301710147/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14175]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14175]

theorem width_14176 : mW 14176 = 339186037156949 := by
  have hu : mW 14176 ≤ 339186037156949 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14176 ≤ 339186037156948 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14176 : RowArithmetic 14176 (1118395469622974828647/1000000000000000000000000) (303671795844642565563553/500000000000000000000000) (7080803473660403/1000000000000000000000000) where
  r0 := (296237099977/500000000000000000)
  k0 := (727785637917427/200000000000000000)
  k6 := (11500686994888689/1000000000000000000)
  q := (168380521438793507497/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14176]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14176]

theorem width_14177 : mW 14177 = 339269788272454 := by
  have hu : mW 14177 ≤ 339269788272454 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14177 ≤ 339269788272453 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14177 : RowArithmetic 14177 (34948916246340572989/31250000000000000000000) (607332499885088524692867/1000000000000000000000000) (7079503512260663/1000000000000000000000000) where
  r0 := (296205757111/500000000000000000)
  k0 := (181936783958479/50000000000000000)
  k6 := (2300056275398649/200000000000000000)
  q := (42096615065822097521/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14177]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14177]

theorem width_14178 : mW 14178 = 339353554158098 := by
  have hu : mW 14178 ≤ 339353554158098 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14178 ≤ 339353554158097 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14178 : RowArithmetic 14178 (223667035452742368933/200000000000000000000000) (151830352409980719998927/250000000000000000000000) (7078203884433837/1000000000000000000000000) where
  r0 := (296174419771/500000000000000000)
  k0 := (363854319251039/100000000000000000)
  k6 := (2874968950503001/250000000000000000)
  q := (168392398878334172867/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14178]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14178]

theorem width_14179 : mW 14179 = 339437334815443 := by
  have hu : mW 14179 ≤ 339437334815443 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14179 ≤ 339437334815442 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14179 : RowArithmetic 14179 (1118305041763214289003/1000000000000000000000000) (24292412838137524742579/40000000000000000000000) (7076904590070059/1000000000000000000000000) where
  r0 := (296143087957/500000000000000000)
  k0 := (3638350729613337/1000000000000000000)
  k6 := (57497351349687/5000000000000000)
  q := (168398337283953014689/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14179]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14179]

theorem width_14180 : mW 14180 = 339521130246051 := by
  have hu : mW 14180 ≤ 339521130246051 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14180 ≤ 339521130246050 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14180 : RowArithmetic 14180 (1118274913379205471947/1000000000000000000000000) (75912404228160522438469/125000000000000000000000) (3537802814529753/500000000000000000000000) where
  r0 := (592223523333/1000000000000000000)
  k0 := (1819079145233417/500000000000000000)
  k6 := (2874766195190467/250000000000000000)
  q := (16840427548016707049/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14180]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14180]

theorem width_14181 : mW 14181 = 339604940451487 := by
  have hu : mW 14181 ≤ 339604940451487 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14181 ≤ 339604940451486 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14181 : RowArithmetic 14181 (1118244792109484436819/1000000000000000000000000) (303644074127555604319587/500000000000000000000000) (7074307001292339/1000000000000000000000000) where
  r0 := (148040220449/250000000000000000)
  k0 := (3637965875065433/1000000000000000000)
  k6 := (2874664833619461/250000000000000000)
  q := (168410213466998491303/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14181]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14181]

theorem width_14182 : mW 14182 = 339688765433312 := by
  have hu : mW 14182 ≤ 339688765433312 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14182 ≤ 339688765433311 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14182 : RowArithmetic 14182 (279553669487963317621/250000000000000000000000) (30363853212128467428523/50000000000000000000000) (7073008706658847/1000000000000000000000000) where
  r0 := (592098251303/1000000000000000000)
  k0 := (454721685426613/125000000000000000)
  k6 := (1437281741384721/125000000000000000)
  q := (33683230248893884851/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14182]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14182]

theorem width_14183 : mW 14183 = 339772605193091 := by
  have hu : mW 14183 ≤ 339772605193091 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14183 ≤ 339772605193090 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14183 : RowArithmetic 14183 (1118184570904112756679/1000000000000000000000000) (303632990893654482994491/500000000000000000000000) (3535855372524641/500000000000000000000000) where
  r0 := (74004453981/125000000000000000)
  k0 := (3637581115494581/1000000000000000000)
  k6 := (11497848570554081/1000000000000000000)
  q := (168422088812602012569/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14183]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14183]

theorem width_14184 : mW 14184 = 339856459732385 := by
  have hu : mW 14184 ≤ 339856459732385 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14184 ≤ 339856459732384 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14184 : RowArithmetic 14184 (1118154470964066720013/1000000000000000000000000) (303627450444490214031851/500000000000000000000000) (7070413116354023/1000000000000000000000000) where
  r0 := (591973023431/1000000000000000000)
  k0 := (3637388771314231/1000000000000000000)
  k6 := (459897730115969/40000000000000000)
  q := (168428026171418395567/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14184]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14184]

theorem width_14185 : mW 14185 = 339940329052758 := by
  have hu : mW 14185 ≤ 339940329052758 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14185 ≤ 339940329052757 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14185 : RowArithmetic 14185 (223624875625903645027/200000000000000000000000) (607243821547234304633687/1000000000000000000000000) (3534557910231717/500000000000000000000000) where
  r0 := (591910426047/1000000000000000000)
  k0 := (1818598225430129/500000000000000000)
  k6 := (2299407595621129/200000000000000000)
  q := (84216981660470354333/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14185]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14185]

theorem width_14186 : mW 14186 = 340024213155773 := by
  have hu : mW 14186 ≤ 340024213155773 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14186 ≤ 340024213155772 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14186 : RowArithmetic 14186 (1118094292398271747851/1000000000000000000000000) (151808185940430297117103/250000000000000000000000) (3533909428633971/500000000000000000000000) where
  r0 := (118369567939/200000000000000000)
  k0 := (3637004154133351/1000000000000000000)
  k6 := (11496632746165787/1000000000000000000)
  q := (168439900261191083383/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14186]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14186]

theorem width_14187 : mW 14187 = 340108112042993 := by
  have hu : mW 14187 ≤ 340108112042993 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14187 ≤ 340108112042992 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14187 : RowArithmetic 14187 (1118064213768132631727/1000000000000000000000000) (607221667532091848408737/1000000000000000000000000) (3533261113329011/500000000000000000000000) where
  r0 := (591785264371/1000000000000000000)
  k0 := (727362376224997/200000000000000000)
  k6 := (114962275570721/10000000000000000)
  q := (168445836992191647337/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14187]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14187]

theorem width_14188 : mW 14188 = 340192025715982 := by
  have hu : mW 14188 ≤ 340192025715982 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14188 ≤ 340192025715981 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14188 : RowArithmetic 14188 (1118034142236906546049/1000000000000000000000000) (121442118571599428182331/200000000000000000000000) (1766306482131043/250000000000000000000000) where
  r0 := (295861350037/500000000000000000)
  k0 := (3636619631835849/1000000000000000000)
  k6 := (11495822410817033/1000000000000000000)
  q := (42112943378491131061/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14188]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14188]

theorem width_14189 : mW 14189 = 340275954176304 := by
  have hu : mW 14189 ≤ 340275954176304 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14189 ≤ 340275954176303 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14189 : RowArithmetic 14189 (559002038901200013933/500000000000000000000000) (607199519739087998318649/1000000000000000000000000) (3531964981378467/500000000000000000000000) where
  r0 := (591660146799/1000000000000000000)
  k0 := (1818213703127169/500000000000000000)
  k6 := (11495417307393039/1000000000000000000)
  q := (6738308393061273357/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14189]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14189]

theorem width_14190 : mW 14190 = 340359897425520 := by
  have hu : mW 14190 ≤ 340359897425520 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14190 ≤ 340359897425519 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14190 : RowArithmetic 14190 (223594804092484421009/200000000000000000000000) (151797112043753870048617/250000000000000000000000) (88282929115587/12500000000000000000000) where
  r0 := (118319520909/200000000000000000)
  k0 := (181811760219057/50000000000000000)
  k6 := (2873753061698143/250000000000000000)
  q := (168463645929915692301/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14190]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14190]

theorem width_14191 : mW 14191 = 340443855465195 := by
  have hu : mW 14191 ≤ 340443855465195 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14191 ≤ 340443855465194 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14191 : RowArithmetic 14191 (223588794042956101181/200000000000000000000000) (607177378165430779620669/1000000000000000000000000) (7061339027884863/1000000000000000000000000) where
  r0 := (591535073309/1000000000000000000)
  k0 := (727208605242159/200000000000000000)
  k6 := (11494607229008087/1000000000000000000)
  q := (168469581824138211399/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14191]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14191]

theorem width_14192 : mW 14192 = 340527828296893 := by
  have hu : mW 14192 ≤ 340527828296893 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14192 ≤ 340527828296892 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14192 : RowArithmetic 14192 (558956963528642183407/500000000000000000000000) (607166309709985164150527/1000000000000000000000000) (7060044058561321/1000000000000000000000000) where
  r0 := (4620879321/7812500000000000)
  k0 := (3635850871737839/1000000000000000000)
  k6 := (5747101127016021/500000000000000000)
  q := (3369510350184429987/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14192]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14192]

theorem width_14193 : mW 14193 = 340611815922176 := by
  have hu : mW 14193 ≤ 340611815922176 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14193 ≤ 340611815922175 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14193 : RowArithmetic 14193 (1117883890987744771131/1000000000000000000000000) (151788810702082500363159/250000000000000000000000) (70587494211671/10000000000000000000000) where
  r0 := (591410043879/1000000000000000000)
  k0 := (363565874095681/100000000000000000)
  k6 := (89795291577007/7812500000000000)
  q := (168481452985187660389/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14193]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14193]

theorem width_14194 : mW 14194 = 340695818342609 := by
  have hu : mW 14194 ≤ 340695818342609 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14194 ≤ 340695818342608 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14194 : RowArithmetic 14194 (279463465500993011293/250000000000000000000000) (607144177460116806764717/1000000000000000000000000) (3528727557796473/500000000000000000000000) where
  r0 := (591347545679/1000000000000000000)
  k0 := (3635466633862241/1000000000000000000)
  k6 := (11493392432475111/1000000000000000000)
  q := (8424369412602939743/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14194]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14194]

theorem width_14195 : mW 14195 = 340779835559755 := by
  have hu : mW 14195 ≤ 340779835559755 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14195 ≤ 340779835559754 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14195 : RowArithmetic 14195 (1117823840103778461361/1000000000000000000000000) (303566556832498597641537/500000000000000000000000) (220505035679053/31250000000000000000000) where
  r0 := (591285058487/1000000000000000000)
  k0 := (1817637275227407/500000000000000000)
  k6 := (229859751717583/20000000000000000)
  q := (42123330827464249803/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14195]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14195]

theorem width_14196 : mW 14196 = 340863867575178 := by
  have hu : mW 14196 ≤ 340863867575178 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14196 ≤ 340863867575177 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14196 : RowArithmetic 14196 (558896912642488308039/500000000000000000000000) (607122051422622813874679/1000000000000000000000000) (3527433749734103/500000000000000000000000) where
  r0 := (591222582299/1000000000000000000)
  k0 := (908770622681497/250000000000000000)
  k6 := (5746291391030739/500000000000000000)
  q := (84249629079302183003/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14196]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14196]

theorem width_14197 : mW 14197 = 340947914390442 := by
  have hu : mW 14197 ≤ 340947914390442 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14197 ≤ 340947914390441 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14197 : RowArithmetic 14197 (558881908772689984967/500000000000000000000000) (151777747683161381329761/250000000000000000000000) (3526787094349691/500000000000000000000000) where
  r0 := (73895014639/125000000000000000)
  k0 := (908722613667573/250000000000000000)
  k6 := (11492178021014561/1000000000000000000)
  q := (42126298199580745977/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14197]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14197]

theorem width_14198 : mW 14198 = 341031976007110 := by
  have hu : mW 14198 ≤ 341031976007110 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14198 ≤ 341031976007109 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14198 : RowArithmetic 14198 (6985836355517521167/6250000000000000000000) (60709993159471726367291/100000000000000000000000) (440767575582137/62500000000000000000000) where
  r0 := (147774415731/250000000000000000)
  k0 := (363469844228533/100000000000000000)
  k6 := (11491773302730869/1000000000000000000)
  q := (84255563614517468849/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14198]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14198]

theorem width_14199 : mW 14199 = 341116052426746 := by
  have hu : mW 14199 ≤ 341116052426746 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14199 ≤ 341116052426745 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14199 : RowArithmetic 14199 (44708152931802482141/40000000000000000000000) (303544437004245003722063/500000000000000000000000) (705098856120363/100000000000000000000000) where
  r0 := (147758804933/250000000000000000)
  k0 := (3634506453565629/1000000000000000000)
  k6 := (1436421078400359/125000000000000000)
  q := (84258530725381154133/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14199]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14199]

theorem width_14200 : mW 14200 = 341200143650915 := by
  have hu : mW 14200 ≤ 341200143650915 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14200 ≤ 341200143650914 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14200 : RowArithmetic 14200 (1117673836779971481403/1000000000000000000000000) (151769454493403978211257/250000000000000000000000) (7049696244258713/1000000000000000000000000) where
  r0 := (590972787533/1000000000000000000)
  k0 := (726862897701143/200000000000000000)
  k6 := (11490963994423043/1000000000000000000)
  q := (168522995463527172613/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14200]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14200]

theorem width_14201 : mW 14201 = 341284249681180 := by
  have hu : mW 14201 ≤ 341284249681180 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14201 ≤ 341284249681179 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14201 : RowArithmetic 14201 (279410964333837280553/250000000000000000000000) (303533381744873633668363/500000000000000000000000) (3524202129185273/500000000000000000000000) where
  r0 := (23636414653/40000000000000000)
  k0 := (3634122547103187/1000000000000000000)
  k6 := (2298111880876771/200000000000000000)
  q := (10533058079209475241/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14201]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14201]

theorem width_14202 : mW 14202 = 341368370519106 := by
  have hu : mW 14202 ≤ 341368370519106 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14202 ≤ 341368370519105 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14202 : RowArithmetic 14202 (279403471239753052987/250000000000000000000000) (121411142111307264475903/200000000000000000000000) (1761778150857559/250000000000000000000000) where
  r0 := (118169591221/200000000000000000)
  k0 := (454241328669071/125000000000000000)
  k6 := (5745077428538893/500000000000000000)
  q := (6741394514490306849/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14202]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14202]

theorem width_14203 : mW 14203 = 341452506166255 := by
  have hu : mW 14203 ≤ 341452506166255 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14203 ≤ 341452506166254 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14203 : RowArithmetic 14203 (1117583919648780463929/1000000000000000000000000) (151761164793408902369219/250000000000000000000000) (3522910639664499/500000000000000000000000) where
  r0 := (59078555687/100000000000000000)
  k0 := (3633738735248381/1000000000000000000)
  k6 := (359054698515541/31250000000000000)
  q := (2633449941379178751/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14203]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14203]

theorem width_14204 : mW 14204 = 341536656624194 := by
  have hu : mW 14204 ≤ 341536656624194 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14204 ≤ 341536656624193 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14204 : RowArithmetic 14204 (279388490350617940137/250000000000000000000000) (607033609340697665468363/1000000000000000000000000) (7044530285957987/1000000000000000000000000) where
  r0 := (295361584309/500000000000000000)
  k0 := (181677343239411/50000000000000000)
  k6 := (2297869178126983/200000000000000000)
  q := (33709345885080594367/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14204]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14204]

theorem width_14205 : mW 14205 = 341620821894485 := by
  have hu : mW 14205 ≤ 341620821894485 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14205 ≤ 341620821894484 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14205 : RowArithmetic 14205 (1117524010217907536767/1000000000000000000000000) (60702256105737517900079/100000000000000000000000) (7043239623208507/1000000000000000000000000) where
  r0 := (118132158269/200000000000000000)
  k0 := (3633355017963529/1000000000000000000)
  k6 := (459557658859323/40000000000000000)
  q := (33710532478737264823/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14205]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14205]

theorem width_14206 : mW 14206 = 341705001978694 := by
  have hu : mW 14206 ≤ 341705001978694 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14206 ≤ 341705001978693 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14206 : RowArithmetic 14206 (1117494066092907935569/1000000000000000000000000) (151752878580830223454109/250000000000000000000000) (440121830685739/62500000000000000000000) where
  r0 := (11811968501/20000000000000000)
  k0 := (145326527790999/40000000000000000)
  k6 := (2872134273758569/250000000000000000)
  q := (84279297576569775301/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14206]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14206]

theorem width_14207 : mW 14207 = 341789196878383 := by
  have hu : mW 14207 ≤ 341789196878383 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14207 ≤ 341789196878382 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14207 : RowArithmetic 14207 (1117464129025296111141/1000000000000000000000000) (607000469138187720603683/1000000000000000000000000) (1760164822284833/250000000000000000000000) where
  r0 := (18454252179/31250000000000000)
  k0 := (3632971395210923/1000000000000000000)
  k6 := (2297626552256201/200000000000000000)
  q := (16856452770378470111/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14207]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14207]

theorem width_14208 : mW 14208 = 341873406595119 := by
  have hu : mW 14208 ≤ 341873406595119 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14208 ≤ 341873406595118 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14208 : RowArithmetic 14208 (1117434199012893389399/1000000000000000000000000) (606989425501628620292699/1000000000000000000000000) (3519684808801183/500000000000000000000000) where
  r0 := (590473725379/1000000000000000000)
  k0 := (908194904818779/250000000000000000)
  k6 := (11487728470215747/1000000000000000000)
  q := (6742818401825752863/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14208]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14208]

theorem width_14209 : mW 14209 = 341957631130465 := by
  have hu : mW 14209 ≤ 341957631130465 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14209 ≤ 341957631130464 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14209 : RowArithmetic 14209 (1117404276053524105703/1000000000000000000000000) (606978383413296707648057/1000000000000000000000000) (7038080276252387/1000000000000000000000000) where
  r0 := (295205695999/500000000000000000)
  k0 := (454073483369489/125000000000000000)
  k6 := (717957763864437/62500000000000000)
  q := (168576392178738954053/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14209]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14209]

theorem width_14210 : mW 14210 = 342041870485986 := by
  have hu : mW 14210 ≤ 342041870485986 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14210 ≤ 342041870485985 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14210 : RowArithmetic 14210 (1117374360145012379571/1000000000000000000000000) (121393468574569046101021/200000000000000000000000) (3518395632490431/500000000000000000000000) where
  r0 := (36896816849/62500000000000000)
  k0 := (3632396138253977/1000000000000000000)
  k6 := (11486920016119231/1000000000000000000)
  q := (84291162051546068361/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14210]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14210]

theorem width_14211 : mW 14211 = 342126124663246 := by
  have hu : mW 14211 ≤ 342126124663246 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14211 ≤ 342126124663245 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14211 : RowArithmetic 14211 (279336112821295931501/250000000000000000000000) (303478151939963708675119/500000000000000000000000) (7035502583679321/1000000000000000000000000) where
  r0 := (590286758133/1000000000000000000)
  k0 := (3632204433160743/1000000000000000000)
  k6 := (11486515853072957/1000000000000000000)
  q := (42147063954681350971/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14211]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14211]

theorem width_14212 : mW 14212 = 342210393663810 := by
  have hu : mW 14212 ≤ 342210393663810 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14212 ≤ 342210393663809 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14212 : RowArithmetic 14212 (1117314549471863981347/1000000000000000000000000) (60694526643419671999451/100000000000000000000000) (175855355805983/25000000000000000000000) where
  r0 := (590224457643/1000000000000000000)
  k0 := (726402550334759/200000000000000000)
  k6 := (2297222346536933/200000000000000000)
  q := (84297093662830392981/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14212]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14212]

theorem width_14213 : mW 14213 = 342294677489242 := by
  have hu : mW 14213 ≤ 342294677489242 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14213 ≤ 342294677489241 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14213 : RowArithmetic 14213 (1117284654702880376113/1000000000000000000000000) (606934230535306653607667/1000000000000000000000000) (3516463105276239/500000000000000000000000) where
  r0 := (36885135507/62500000000000000)
  k0 := (3631821093790717/1000000000000000000)
  k6 := (229714153098937/20000000000000000)
  q := (168600118623920309507/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14213]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14213]

theorem width_14214 : mW 14214 = 342378976141108 := by
  have hu : mW 14214 ≤ 342378976141108 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14214 ≤ 342378976141107 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14214 : RowArithmetic 14214 (1117254766976059925867/1000000000000000000000000) (12138463923658217327269/20000000000000000000000) (351581925925521/50000000000000000000000) where
  r0 := (4610155387/7812500000000000)
  k0 := (1815814729751469/500000000000000000)
  k6 := (11485303619852013/1000000000000000000)
  q := (168606049713525997193/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14214]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14214]

theorem width_14215 : mW 14215 = 342463289620971 := by
  have hu : mW 14215 ≤ 342463289620971 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14215 ≤ 342463289620970 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14215 : RowArithmetic 14215 (1117224886289232111187/1000000000000000000000000) (606912163376663056803271/1000000000000000000000000) (3515175578002437/500000000000000000000000) where
  r0 := (73754702739/125000000000000000)
  k0 := (3631437848804961/1000000000000000000)
  k6 := (2871224906848163/250000000000000000)
  q := (168611980594499867823/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14215]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14215]

theorem width_14216 : mW 14216 = 342547617930398 := by
  have hu : mW 14216 ≤ 342547617930398 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14216 ≤ 342547617930397 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14216 : RowArithmetic 14216 (34912344145007035187/31250000000000000000000) (303450566058108558353459/500000000000000000000000) (3514532061463767/500000000000000000000000) where
  r0 := (589975365239/1000000000000000000)
  k0 := (3631246261697443/1000000000000000000)
  k6 := (11484495677561269/1000000000000000000)
  q := (84308955633431968163/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14216]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14216]

theorem width_14217 : mW 14217 = 342631961070952 := by
  have hu : mW 14217 ≤ 342631961070952 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14217 ≤ 342631961070951 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14217 : RowArithmetic 14217 (558582573013435081537/500000000000000000000000) (606890102401226942363983/1000000000000000000000000) (7027777419170219/1000000000000000000000000) where
  r0 := (589913119513/1000000000000000000)
  k0 := (3631054698171807/1000000000000000000)
  k6 := (1148409177035037/100000000000000000)
  q := (168623841730640213759/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14217]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14217]

theorem width_14218 : mW 14218 = 342716319044199 := by
  have hu : mW 14218 ≤ 342716319044199 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14218 ≤ 342716319044198 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14218 : RowArithmetic 14218 (558567643223498832237/500000000000000000000000) (606879074231346631055203/1000000000000000000000000) (7026491044624729/1000000000000000000000000) where
  r0 := (147462721183/250000000000000000)
  k0 := (3630863158225631/1000000000000000000)
  k6 := (11483687905752459/1000000000000000000)
  q := (10539360749115669207/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14218]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14218]

theorem width_14219 : mW 14219 = 342800691851704 := by
  have hu : mW 14219 ≤ 342800691851704 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14219 ≤ 342800691851703 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14219 : RowArithmetic 14219 (279276358474609865827/250000000000000000000000) (303434023803115159743027/500000000000000000000000) (7025204999182933/1000000000000000000000000) where
  r0 := (147447165223/250000000000000000)
  k0 := (726134328370067/200000000000000000)
  k6 := (2870821020940011/250000000000000000)
  q := (1686357020325174203/10000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14219]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14219]

theorem width_14220 : mW 14220 = 342885079495031 := by
  have hu : mW 14220 ≤ 342885079495031 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14220 ≤ 342885079495030 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14220 : RowArithmetic 14220 (1117075588379028782277/1000000000000000000000000) (606857022525532259851207/1000000000000000000000000) (3511959641368381/500000000000000000000000) where
  r0 := (73715805999/125000000000000000)
  k0 := (363048014904657/100000000000000000)
  k6 := (5741440152182817/500000000000000000)
  q := (6745665274826494087/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14220]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14220]

theorem width_14221 : mW 14221 = 342969481975746 := by
  have hu : mW 14221 ≤ 342969481975746 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14221 ≤ 342969481975745 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14221 : RowArithmetic 14221 (279261437471649657287/250000000000000000000000) (606845998988906841446119/1000000000000000000000000) (7022633895178151/1000000000000000000000000) where
  r0 := (589664246029/1000000000000000000)
  k0 := (56723260622013/15625000000000000)
  k6 := (11482476567561741/1000000000000000000)
  q := (168647561500307498517/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14221]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14221]

theorem width_14222 : mW 14222 = 343053899295414 := by
  have hu : mW 14222 ≤ 343053899295414 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14222 ≤ 343053899295413 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14222 : RowArithmetic 14222 (1117015918418983400837/1000000000000000000000000) (606834976996008531701859/1000000000000000000000000) (7021348836399101/1000000000000000000000000) where
  r0 := (117920411/200000000000000)
  k0 := (726019446826323/200000000000000000)
  k6 := (11482072873340879/1000000000000000000)
  q := (84326745460737425521/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14222]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14222]

theorem width_14223 : mW 14223 = 343138331455601 := by
  have hu : mW 14223 ≤ 343138331455601 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14223 ≤ 343138331455600 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14223 : RowArithmetic 14223 (279246523493504453523/250000000000000000000000) (606823956546491958951663/1000000000000000000000000) (1404012821258327/200000000000000000000000) where
  r0 := (589539874901/1000000000000000000)
  k0 := (3629905812006333/1000000000000000000)
  k6 := (11481669221695561/1000000000000000000)
  q := (210824275167732997/1250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14223]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14223]

theorem width_14224 : mW 14224 = 343222778457870 := by
  have hu : mW 14224 ≤ 343222778457870 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14224 ≤ 343222778457869 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14224 : RowArithmetic 14224 (1116956276549539040839/1000000000000000000000000) (30340646882000588018869/50000000000000000000000) (1403755940949577/200000000000000000000000) where
  r0 := (147369426433/250000000000000000)
  k0 := (3629714413436711/1000000000000000000)
  k6 := (2296253122523661/200000000000000000)
  q := (84332674569232061087/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14224]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14224]

theorem width_14225 : mW 14225 = 343307240303789 := by
  have hu : mW 14225 ≤ 343307240303789 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14225 ≤ 343307240303788 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14225 : RowArithmetic 14225 (139615808267922804607/125000000000000000000000) (606801920276222755735239/1000000000000000000000000) (3508747815829961/500000000000000000000000) where
  r0 := (18419235859/31250000000000000)
  k0 := (3629523038411081/1000000000000000000)
  k6 := (11480862046101629/1000000000000000000)
  q := (84335638967165002443/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14225]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14225]

theorem width_14226 : mW 14226 = 343391716994921 := by
  have hu : mW 14226 ≤ 343391716994921 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14226 ≤ 343391716994920 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14226 : RowArithmetic 14226 (139612082844173359891/125000000000000000000000) (151697726113694961615863/250000000000000000000000) (1754052971729991/250000000000000000000000) where
  r0 := (589353400167/1000000000000000000)
  k0 := (362933168692701/100000000000000000)
  k6 := (5740229261069027/500000000000000000)
  q := (84338603260903010997/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14226]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14226]

theorem width_14227 : mW 14227 = 343476208532833 := by
  have hu : mW 14227 ≤ 343476208532833 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14227 ≤ 343476208532832 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14227 : RowArithmetic 14227 (44674674655095598513/40000000000000000000000) (606779890175338015790917/1000000000000000000000000) (3507464235210097/500000000000000000000000) where
  r0 := (589291263767/1000000000000000000)
  k0 := (3629140358982063/1000000000000000000)
  k6 := (11480055040720103/1000000000000000000)
  q := (84341567450457072947/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14227]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14227]

theorem width_14228 : mW 14228 = 343560714919090 := by
  have hu : mW 14228 ≤ 343560714919090 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14228 ≤ 343560714919089 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14228 : RowArithmetic 14228 (1116837077013231202007/1000000000000000000000000) (303384438718776212265919/500000000000000000000000) (7013645382052877/1000000000000000000000000) where
  r0 := (147307284571/250000000000000000)
  k0 := (725789810913529/200000000000000000)
  k6 := (11479651601840299/1000000000000000000)
  q := (1054306644197977157/6250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14228]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14228]

theorem width_14229 : mW 14229 = 343645236155258 := by
  have hu : mW 14229 ≤ 343645236155258 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14229 ≤ 343645236155257 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14229 : RowArithmetic 14229 (1116807294658750429283/1000000000000000000000000) (15168946656026956532159/25000000000000000000000) (219136331928447/31250000000000000000000) where
  r0 := (589167023717/1000000000000000000)
  k0 := (3628757773684399/1000000000000000000)
  k6 := (358726506421599/31250000000000000)
  q := (42173747758528646087/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14229]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14229]

theorem width_14230 : mW 14230 = 343729772242902 := by
  have hu : mW 14230 ≤ 343729772242902 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14230 ≤ 343729772242901 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14230 : RowArithmetic 14230 (139597189913973607647/125000000000000000000000) (303373428292785430799513/500000000000000000000000) (7011080189284829/1000000000000000000000000) where
  r0 := (294552460031/500000000000000000)
  k0 := (1814283258161863/500000000000000000)
  k6 := (11478844851665239/1000000000000000000)
  q := (168700918788250824393/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14230]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14230]

theorem width_14231 : mW 14231 = 343814323183587 := by
  have hu : mW 14231 ≤ 343814323183587 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14231 ≤ 343814323183586 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14231 : RowArithmetic 14231 (1116747750970188564467/1000000000000000000000000) (121347169694137131459279/200000000000000000000000) (7009798084668853/1000000000000000000000000) where
  r0 := (589042827317/1000000000000000000)
  k0 := (907093820620797/250000000000000000)
  k6 := (11478441540355041/1000000000000000000)
  q := (33741369266821404443/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14231]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14231]

theorem width_14232 : mW 14232 = 343898888978880 := by
  have hu : mW 14232 ≤ 343898888978880 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14232 ≤ 343898888978879 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14232 : RowArithmetic 14232 (111671798963179139191/100000000000000000000000) (606724841896078160787747/1000000000000000000000000) (7008516307754777/1000000000000000000000000) where
  r0 := (588980745479/1000000000000000000)
  k0 := (1814092036078631/500000000000000000)
  k6 := (2295607654310621/200000000000000000)
  q := (5272274177240785341/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14232]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14232]

theorem width_14233 : mW 14233 = 343983469630347 := by
  have hu : mW 14233 ≤ 343983469630347 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14233 ≤ 343983469630346 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14233 : RowArithmetic 14233 (558344117647220289549/500000000000000000000000) (151678459215351012848761/250000000000000000000000) (7007234858435069/1000000000000000000000000) where
  r0 := (117783734909/200000000000000000)
  k0 := (3627992885340427/1000000000000000000)
  k6 := (2295527009050393/200000000000000000)
  q := (16871870080106709973/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14233]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14233]

theorem width_14234 : mW 14234 = 344068065139552 := by
  have hu : mW 14234 ≤ 344068065139552 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14234 ≤ 344068065139551 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14234 : RowArithmetic 14234 (279164621988995318607/250000000000000000000000) (6067028333663190435233/10000000000000000000000) (7005953736602281/1000000000000000000000000) where
  r0 := (588856614513/1000000000000000000)
  k0 := (3627801722030237/1000000000000000000)
  k6 := (2869307965361039/250000000000000000)
  q := (84362313861107437029/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14234]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14234]

theorem width_14235 : mW 14235 = 344152675508063 := by
  have hu : mW 14235 ≤ 344152675508063 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14235 ≤ 344152675508062 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14235 : RowArithmetic 14235 (279157186903564337217/250000000000000000000000) (75836478926309876119251/125000000000000000000000) (109448014721077/15625000000000000000000) where
  r0 := (29439728269/50000000000000000)
  k0 := (226725661388823/62500000000000000)
  k6 := (1434603590015277/125000000000000000)
  q := (168730554435170395431/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14235]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14235]

theorem width_14236 : mW 14236 = 344237300737444 := by
  have hu : mW 14236 ≤ 344237300737444 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14236 ≤ 344237300737443 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14236 : RowArithmetic 14236 (69787438391694728019/62500000000000000000000) (303340415496769965056763/500000000000000000000000) (7003392474967651/1000000000000000000000000) where
  r0 := (588732527143/1000000000000000000)
  k0 := (3627419465907693/1000000000000000000)
  k6 := (5738212810639341/500000000000000000)
  q := (168736480939955601529/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14236]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14236]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 14162 then ⟨(1118818314912379507887/1000000000000000000000000), (60749904084261492123691/100000000000000000000000), (3549519010027327/500000000000000000000000)⟩ else
  if n = 14163 then ⟨(559394032624104361279/500000000000000000000000), (607487927175161454704551/1000000000000000000000000), (7097733377071309/1000000000000000000000000)⟩ else
  if n = 14164 then ⟨(559378911367919163447/500000000000000000000000), (303738407535826010927793/500000000000000000000000), (354821453460197/50000000000000000000000)⟩ else
  if n = 14165 then ⟨(139840948421631741183/125000000000000000000000), (303732852265867463916679/500000000000000000000000), (7095125096341999/1000000000000000000000000)⟩ else
  if n = 14166 then ⟨(559348679578821828223/500000000000000000000000), (7593182444438233957377/12500000000000000000000), (141876429167501/20000000000000000000000)⟩ else
  if n = 14167 then ⟨(1118667138087395962597/1000000000000000000000000), (607443488141271941881947/1000000000000000000000000), (7092518155192679/1000000000000000000000000)⟩ else
  if n = 14168 then ⟨(111863692416009963193/100000000000000000000000), (121486476458004657037131/200000000000000000000000), (3545607593342249/500000000000000000000000)⟩ else
  if n = 14169 then ⟨(69912919835846554381/62500000000000000000000), (607421278000961550033107/1000000000000000000000000), (3544956276370093/500000000000000000000000)⟩ else
  if n = 14170 then ⟨(1118576517725522757183/1000000000000000000000000), (607410175273735663187729/1000000000000000000000000), (1417722050649893/200000000000000000000000)⟩ else
  if n = 14171 then ⟨(34954572662932056021/31250000000000000000000), (151849768526998650939421/250000000000000000000000), (442956768006383/62500000000000000000000)⟩ else
  if n = 14172 then ⟨(1118516139836245167977/1000000000000000000000000), (303693987251693751237781/500000000000000000000000), (1771501664296981/250000000000000000000000)⟩ else
  if n = 14173 then ⟨(1118485961590575130121/1000000000000000000000000), (151844219114890912955949/250000000000000000000000), (110698521256199/15625000000000000000000)⟩ else
  if n = 14174 then ⟨(1118455790474609708419/1000000000000000000000000), (303682889988086150974823/500000000000000000000000), (442712774851153/62500000000000000000000)⟩ else
  if n = 14175 then ⟨(559212813243072174897/500000000000000000000000), (607354685052862941651399/1000000000000000000000000), (1770525942185753/250000000000000000000000)⟩ else
  if n = 14176 then ⟨(1118395469622974828647/1000000000000000000000000), (303671795844642565563553/500000000000000000000000), (7080803473660403/1000000000000000000000000)⟩ else
  if n = 14177 then ⟨(34948916246340572989/31250000000000000000000), (607332499885088524692867/1000000000000000000000000), (7079503512260663/1000000000000000000000000)⟩ else
  if n = 14178 then ⟨(223667035452742368933/200000000000000000000000), (151830352409980719998927/250000000000000000000000), (7078203884433837/1000000000000000000000000)⟩ else
  if n = 14179 then ⟨(1118305041763214289003/1000000000000000000000000), (24292412838137524742579/40000000000000000000000), (7076904590070059/1000000000000000000000000)⟩ else
  if n = 14180 then ⟨(1118274913379205471947/1000000000000000000000000), (75912404228160522438469/125000000000000000000000), (3537802814529753/500000000000000000000000)⟩ else
  if n = 14181 then ⟨(1118244792109484436819/1000000000000000000000000), (303644074127555604319587/500000000000000000000000), (7074307001292339/1000000000000000000000000)⟩ else
  if n = 14182 then ⟨(279553669487963317621/250000000000000000000000), (30363853212128467428523/50000000000000000000000), (7073008706658847/1000000000000000000000000)⟩ else
  if n = 14183 then ⟨(1118184570904112756679/1000000000000000000000000), (303632990893654482994491/500000000000000000000000), (3535855372524641/500000000000000000000000)⟩ else
  if n = 14184 then ⟨(1118154470964066720013/1000000000000000000000000), (303627450444490214031851/500000000000000000000000), (7070413116354023/1000000000000000000000000)⟩ else
  if n = 14185 then ⟨(223624875625903645027/200000000000000000000000), (607243821547234304633687/1000000000000000000000000), (3534557910231717/500000000000000000000000)⟩ else
  if n = 14186 then ⟨(1118094292398271747851/1000000000000000000000000), (151808185940430297117103/250000000000000000000000), (3533909428633971/500000000000000000000000)⟩ else
  if n = 14187 then ⟨(1118064213768132631727/1000000000000000000000000), (607221667532091848408737/1000000000000000000000000), (3533261113329011/500000000000000000000000)⟩ else
  if n = 14188 then ⟨(1118034142236906546049/1000000000000000000000000), (121442118571599428182331/200000000000000000000000), (1766306482131043/250000000000000000000000)⟩ else
  if n = 14189 then ⟨(559002038901200013933/500000000000000000000000), (607199519739087998318649/1000000000000000000000000), (3531964981378467/500000000000000000000000)⟩ else
  if n = 14190 then ⟨(223594804092484421009/200000000000000000000000), (151797112043753870048617/250000000000000000000000), (88282929115587/12500000000000000000000)⟩ else
  if n = 14191 then ⟨(223588794042956101181/200000000000000000000000), (607177378165430779620669/1000000000000000000000000), (7061339027884863/1000000000000000000000000)⟩ else
  if n = 14192 then ⟨(558956963528642183407/500000000000000000000000), (607166309709985164150527/1000000000000000000000000), (7060044058561321/1000000000000000000000000)⟩ else
  if n = 14193 then ⟨(1117883890987744771131/1000000000000000000000000), (151788810702082500363159/250000000000000000000000), (70587494211671/10000000000000000000000)⟩ else
  if n = 14194 then ⟨(279463465500993011293/250000000000000000000000), (607144177460116806764717/1000000000000000000000000), (3528727557796473/500000000000000000000000)⟩ else
  if n = 14195 then ⟨(1117823840103778461361/1000000000000000000000000), (303566556832498597641537/500000000000000000000000), (220505035679053/31250000000000000000000)⟩ else
  if n = 14196 then ⟨(558896912642488308039/500000000000000000000000), (607122051422622813874679/1000000000000000000000000), (3527433749734103/500000000000000000000000)⟩ else
  if n = 14197 then ⟨(558881908772689984967/500000000000000000000000), (151777747683161381329761/250000000000000000000000), (3526787094349691/500000000000000000000000)⟩ else
  if n = 14198 then ⟨(6985836355517521167/6250000000000000000000), (60709993159471726367291/100000000000000000000000), (440767575582137/62500000000000000000000)⟩ else
  if n = 14199 then ⟨(44708152931802482141/40000000000000000000000), (303544437004245003722063/500000000000000000000000), (705098856120363/100000000000000000000000)⟩ else
  if n = 14200 then ⟨(1117673836779971481403/1000000000000000000000000), (151769454493403978211257/250000000000000000000000), (7049696244258713/1000000000000000000000000)⟩ else
  if n = 14201 then ⟨(279410964333837280553/250000000000000000000000), (303533381744873633668363/500000000000000000000000), (3524202129185273/500000000000000000000000)⟩ else
  if n = 14202 then ⟨(279403471239753052987/250000000000000000000000), (121411142111307264475903/200000000000000000000000), (1761778150857559/250000000000000000000000)⟩ else
  if n = 14203 then ⟨(1117583919648780463929/1000000000000000000000000), (151761164793408902369219/250000000000000000000000), (3522910639664499/500000000000000000000000)⟩ else
  if n = 14204 then ⟨(279388490350617940137/250000000000000000000000), (607033609340697665468363/1000000000000000000000000), (7044530285957987/1000000000000000000000000)⟩ else
  if n = 14205 then ⟨(1117524010217907536767/1000000000000000000000000), (60702256105737517900079/100000000000000000000000), (7043239623208507/1000000000000000000000000)⟩ else
  if n = 14206 then ⟨(1117494066092907935569/1000000000000000000000000), (151752878580830223454109/250000000000000000000000), (440121830685739/62500000000000000000000)⟩ else
  if n = 14207 then ⟨(1117464129025296111141/1000000000000000000000000), (607000469138187720603683/1000000000000000000000000), (1760164822284833/250000000000000000000000)⟩ else
  if n = 14208 then ⟨(1117434199012893389399/1000000000000000000000000), (606989425501628620292699/1000000000000000000000000), (3519684808801183/500000000000000000000000)⟩ else
  if n = 14209 then ⟨(1117404276053524105703/1000000000000000000000000), (606978383413296707648057/1000000000000000000000000), (7038080276252387/1000000000000000000000000)⟩ else
  if n = 14210 then ⟨(1117374360145012379571/1000000000000000000000000), (121393468574569046101021/200000000000000000000000), (3518395632490431/500000000000000000000000)⟩ else
  if n = 14211 then ⟨(279336112821295931501/250000000000000000000000), (303478151939963708675119/500000000000000000000000), (7035502583679321/1000000000000000000000000)⟩ else
  if n = 14212 then ⟨(1117314549471863981347/1000000000000000000000000), (60694526643419671999451/100000000000000000000000), (175855355805983/25000000000000000000000)⟩ else
  if n = 14213 then ⟨(1117284654702880376113/1000000000000000000000000), (606934230535306653607667/1000000000000000000000000), (3516463105276239/500000000000000000000000)⟩ else
  if n = 14214 then ⟨(1117254766976059925867/1000000000000000000000000), (12138463923658217327269/20000000000000000000000), (351581925925521/50000000000000000000000)⟩ else
  if n = 14215 then ⟨(1117224886289232111187/1000000000000000000000000), (606912163376663056803271/1000000000000000000000000), (3515175578002437/500000000000000000000000)⟩ else
  if n = 14216 then ⟨(34912344145007035187/31250000000000000000000), (303450566058108558353459/500000000000000000000000), (3514532061463767/500000000000000000000000)⟩ else
  if n = 14217 then ⟨(558582573013435081537/500000000000000000000000), (606890102401226942363983/1000000000000000000000000), (7027777419170219/1000000000000000000000000)⟩ else
  if n = 14218 then ⟨(558567643223498832237/500000000000000000000000), (606879074231346631055203/1000000000000000000000000), (7026491044624729/1000000000000000000000000)⟩ else
  if n = 14219 then ⟨(279276358474609865827/250000000000000000000000), (303434023803115159743027/500000000000000000000000), (7025204999182933/1000000000000000000000000)⟩ else
  if n = 14220 then ⟨(1117075588379028782277/1000000000000000000000000), (606857022525532259851207/1000000000000000000000000), (3511959641368381/500000000000000000000000)⟩ else
  if n = 14221 then ⟨(279261437471649657287/250000000000000000000000), (606845998988906841446119/1000000000000000000000000), (7022633895178151/1000000000000000000000000)⟩ else
  if n = 14222 then ⟨(1117015918418983400837/1000000000000000000000000), (606834976996008531701859/1000000000000000000000000), (7021348836399101/1000000000000000000000000)⟩ else
  if n = 14223 then ⟨(279246523493504453523/250000000000000000000000), (606823956546491958951663/1000000000000000000000000), (1404012821258327/200000000000000000000000)⟩ else
  if n = 14224 then ⟨(1116956276549539040839/1000000000000000000000000), (30340646882000588018869/50000000000000000000000), (1403755940949577/200000000000000000000000)⟩ else
  if n = 14225 then ⟨(139615808267922804607/125000000000000000000000), (606801920276222755735239/1000000000000000000000000), (3508747815829961/500000000000000000000000)⟩ else
  if n = 14226 then ⟨(139612082844173359891/125000000000000000000000), (151697726113694961615863/250000000000000000000000), (1754052971729991/250000000000000000000000)⟩ else
  if n = 14227 then ⟨(44674674655095598513/40000000000000000000000), (606779890175338015790917/1000000000000000000000000), (3507464235210097/500000000000000000000000)⟩ else
  if n = 14228 then ⟨(1116837077013231202007/1000000000000000000000000), (303384438718776212265919/500000000000000000000000), (7013645382052877/1000000000000000000000000)⟩ else
  if n = 14229 then ⟨(1116807294658750429283/1000000000000000000000000), (15168946656026956532159/25000000000000000000000), (219136331928447/31250000000000000000000)⟩ else
  if n = 14230 then ⟨(139597189913973607647/125000000000000000000000), (303373428292785430799513/500000000000000000000000), (7011080189284829/1000000000000000000000000)⟩ else
  if n = 14231 then ⟨(1116747750970188564467/1000000000000000000000000), (121347169694137131459279/200000000000000000000000), (7009798084668853/1000000000000000000000000)⟩ else
  if n = 14232 then ⟨(111671798963179139191/100000000000000000000000), (606724841896078160787747/1000000000000000000000000), (7008516307754777/1000000000000000000000000)⟩ else
  if n = 14233 then ⟨(558344117647220289549/500000000000000000000000), (151678459215351012848761/250000000000000000000000), (7007234858435069/1000000000000000000000000)⟩ else
  if n = 14234 then ⟨(279164621988995318607/250000000000000000000000), (6067028333663190435233/10000000000000000000000), (7005953736602281/1000000000000000000000000)⟩ else
  if n = 14235 then ⟨(279157186903564337217/250000000000000000000000), (75836478926309876119251/125000000000000000000000), (109448014721077/15625000000000000000000)⟩ else
  ⟨(69787438391694728019/62500000000000000000000), (303340415496769965056763/500000000000000000000000), (7003392474967651/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14162 ≤ n) (hb : n ≤ 14236) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14162
  · exact row_14163
  · exact row_14164
  · exact row_14165
  · exact row_14166
  · exact row_14167
  · exact row_14168
  · exact row_14169
  · exact row_14170
  · exact row_14171
  · exact row_14172
  · exact row_14173
  · exact row_14174
  · exact row_14175
  · exact row_14176
  · exact row_14177
  · exact row_14178
  · exact row_14179
  · exact row_14180
  · exact row_14181
  · exact row_14182
  · exact row_14183
  · exact row_14184
  · exact row_14185
  · exact row_14186
  · exact row_14187
  · exact row_14188
  · exact row_14189
  · exact row_14190
  · exact row_14191
  · exact row_14192
  · exact row_14193
  · exact row_14194
  · exact row_14195
  · exact row_14196
  · exact row_14197
  · exact row_14198
  · exact row_14199
  · exact row_14200
  · exact row_14201
  · exact row_14202
  · exact row_14203
  · exact row_14204
  · exact row_14205
  · exact row_14206
  · exact row_14207
  · exact row_14208
  · exact row_14209
  · exact row_14210
  · exact row_14211
  · exact row_14212
  · exact row_14213
  · exact row_14214
  · exact row_14215
  · exact row_14216
  · exact row_14217
  · exact row_14218
  · exact row_14219
  · exact row_14220
  · exact row_14221
  · exact row_14222
  · exact row_14223
  · exact row_14224
  · exact row_14225
  · exact row_14226
  · exact row_14227
  · exact row_14228
  · exact row_14229
  · exact row_14230
  · exact row_14231
  · exact row_14232
  · exact row_14233
  · exact row_14234
  · exact row_14235
  · exact row_14236

end BstLean.Part271.R3.Rows14162
