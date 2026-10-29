import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 13301–13375. -/
namespace BstLean.Part271.R3.Rows13301
open Real BstLean.Part130 BstLean.Part227

theorem width_13301 : mW 13301 = 271390741186056 := by
  have hu : mW 13301 ≤ 271390741186056 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13301 ≤ 271390741186055 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13301 : RowArithmetic 13301 (1147774687460822008137/1000000000000000000000000) (617688492504094576313473/1000000000000000000000000) (8359607491598489/1000000000000000000000000) where
  r0 := (651888860419/1000000000000000000)
  k0 := (381702973925599/100000000000000000)
  k6 := (11872945910689163/1000000000000000000)
  q := (163101195581148331447/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13301]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13301]

theorem width_13302 : mW 13302 = 271462161144259 := by
  have hu : mW 13302 ≤ 271462161144259 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13302 ≤ 271462161144258 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13302 : RowArithmetic 13302 (1147737358672637057621/1000000000000000000000000) (61767588915559544081067/100000000000000000000000) (2089492005328403/250000000000000000000000) where
  r0 := (130363070311/200000000000000000)
  k0 := (3816814523559437/1000000000000000000)
  k6 := (5936249809030847/500000000000000000)
  q := (163107326628818240833/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13302]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13302]

theorem width_13303 : mW 13303 = 271533594526510 := by
  have hu : mW 13303 ≤ 271533594526510 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13303 ≤ 271533594526509 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13303 : RowArithmetic 13303 (143462504912776694323/125000000000000000000000) (617663287719059210378931/1000000000000000000000000) (1044541125043251/125000000000000000000000) where
  r0 := (130348371301/200000000000000000)
  k0 := (763319867234877/200000000000000000)
  k6 := (5936026687878787/500000000000000000)
  q := (16311345744603662223/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13303]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13303]

theorem width_13304 : mW 13304 = 271605041334322 := by
  have hu : mW 13304 ≤ 271605041334322 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13304 ≤ 271605041334321 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13304 : RowArithmetic 13304 (14345784116830532131/12500000000000000000000) (61765068819402276978201/100000000000000000000000) (4177345214268823/500000000000000000000000) where
  r0 := (130333675053/200000000000000000)
  k0 := (3816384177093909/1000000000000000000)
  k6 := (2967901795941837/250000000000000000)
  q := (81559794016414730031/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13304]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13304]

theorem width_13305 : mW 13305 = 271676501569208 := by
  have hu : mW 13305 ≤ 271676501569208 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13305 ≤ 271676501569207 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13305 : RowArithmetic 13305 (1147625428802216488711/1000000000000000000000000) (154409522645005783413571/250000000000000000000000) (8353052305730563/1000000000000000000000000) where
  r0 := (81449363479/125000000000000000)
  k0 := (3816169046314013/1000000000000000000)
  k6 := (296779026052039/25000000000000000)
  q := (163125718389222733869/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13305]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13305]

theorem width_13306 : mW 13306 = 271747975232683 := by
  have hu : mW 13306 ≤ 271747975232683 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13306 ≤ 271747975232682 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13306 : RowArithmetic 13306 (1147588137666427429171/1000000000000000000000000) (38601593429787347563421/62500000000000000000000) (2087853657941701/250000000000000000000000) where
  r0 := (325760727101/500000000000000000)
  k0 := (3815953943827769/1000000000000000000)
  k6 := (11870714950690761/1000000000000000000)
  q := (163131848515242418313/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13306]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13306]

theorem width_13307 : mW 13307 = 271819462326261 := by
  have hu : mW 13307 ≤ 271819462326261 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13307 ≤ 271819462326260 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13307 : RowArithmetic 13307 (573775427967984806033/500000000000000000000000) (617612901083283384072903/1000000000000000000000000) (4174888703244257/500000000000000000000000) where
  r0 := (162862003593/250000000000000000)
  k0 := (476967358703897/125000000000000000)
  k6 := (11870268909585499/1000000000000000000)
  q := (40784494602728620793/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13307]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13307]

theorem width_13308 : mW 13308 = 271890962851455 := by
  have hu : mW 13308 ≤ 271890962851455 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13308 ≤ 271890962851454 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13308 : RowArithmetic 13308 (286878395901934838869/250000000000000000000000) (154400077299904523276511/250000000000000000000000) (8348140629737939/1000000000000000000000000) where
  r0 := (325687294169/500000000000000000)
  k0 := (1907761911858651/500000000000000000)
  k6 := (11869822918756329/1000000000000000000)
  q := (163144108076264893349/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13308]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13308]

theorem width_13309 : mW 13309 = 271962476809780 := by
  have hu : mW 13309 ≤ 271962476809780 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13309 ≤ 271962476809779 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13309 : RowArithmetic 13309 (143434540084829089237/125000000000000000000000) (308793859612569678810103/500000000000000000000000) (8346504301357333/1000000000000000000000000) where
  r0 := (20353161753/31250000000000000)
  k0 := (763061761215843/200000000000000000)
  k6 := (5934688489096903/500000000000000000)
  q := (163150237511319608867/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13309]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13309]

theorem width_13310 : mW 13310 = 272034004202750 := by
  have hu : mW 13310 ≤ 272034004202750 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13310 ≤ 272034004202749 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13310 : RowArithmetic 13310 (229487813429109567791/200000000000000000000000) (617575131159385005133341/1000000000000000000000000) (8344868421189049/1000000000000000000000000) where
  r0 := (325613888821/500000000000000000)
  k0 := (1907546908354989/500000000000000000)
  k6 := (11868931087888489/1000000000000000000)
  q := (20394545839513073109/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13310]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13310]

theorem width_13311 : mW 13311 = 272105545031879 := by
  have hu : mW 13311 ≤ 272105545031879 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13311 ≤ 272105545031878 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13311 : RowArithmetic 13311 (1147401823005384191329/1000000000000000000000000) (7719531812523662470737/12500000000000000000000) (834323298907551/100000000000000000000000) where
  r0 := (325577196487/500000000000000000)
  k0 := (3814878855608511/1000000000000000000)
  k6 := (11868485247830939/1000000000000000000)
  q := (81581247845322885819/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13311]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13311]

theorem width_13312 : mW 13312 = 272177099298681 := by
  have hu : mW 13312 ≤ 272177099298681 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13312 ≤ 272177099298680 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13312 : RowArithmetic 13312 (45894583530201701601/40000000000000000000000) (15438749018805036342069/25000000000000000000000) (834159800485921/100000000000000000000000) where
  r0 := (651081022087/1000000000000000000)
  k0 := (3814663922764947/1000000000000000000)
  k6 := (11868039458011719/1000000000000000000)
  q := (163168624434969114561/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13312]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13312]

theorem width_13313 : mW 13313 = 272248667004671 := by
  have hu : mW 13313 ≤ 272248667004671 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13313 ≤ 272248667004670 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13313 : RowArithmetic 13313 (143415920361428022089/125000000000000000000000) (308768689204924328177713/500000000000000000000000) (8339963468382679/1000000000000000000000000) where
  r0 := (325503832489/500000000000000000)
  k0 := (3814449018175273/1000000000000000000)
  k6 := (5933796859210697/500000000000000000)
  q := (16317475294910055417/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13313]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13313]

theorem width_13314 : mW 13314 = 272320248151363 := by
  have hu : mW 13314 ≤ 272320248151363 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13314 ≤ 272320248151362 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13314 : RowArithmetic 13314 (1147290146911432485959/1000000000000000000000000) (61752479797437301353641/100000000000000000000000) (2084582344872137/250000000000000000000000) where
  r0 := (650934321643/1000000000000000000)
  k0 := (762846828366509/200000000000000000)
  k6 := (11867148029050533/1000000000000000000)
  q := (163180881233066026117/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13314]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13314]

theorem width_13315 : mW 13315 = 272391842740272 := by
  have hu : mW 13315 ≤ 272391842740272 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13315 ≤ 272391842740271 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13315 : RowArithmetic 13315 (71703308769498210891/62500000000000000000000) (38594513715332072994467/62500000000000000000000) (8336695738019487/1000000000000000000000000) where
  r0 := (650860992079/1000000000000000000)
  k0 := (3814019293732749/1000000000000000000)
  k6 := (5933351194944853/500000000000000000)
  q := (40796752321722865297/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13315]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13315]

theorem width_13316 : mW 13316 = 272463450772911 := by
  have hu : mW 13316 ≤ 272463450772911 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13316 ≤ 272463450772910 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13316 : RowArithmetic 13316 (35850491971560863213/31250000000000000000000) (123499928564441551402721/200000000000000000000000) (1041882817977287/125000000000000000000000) where
  r0 := (650787676281/1000000000000000000)
  k0 := (762760894773201/200000000000000000)
  k6 := (11866256800929487/1000000000000000000)
  q := (1631931371106027853/10000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13316]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13316]

theorem width_13317 : mW 13317 = 272535072250795 := by
  have hu : mW 13317 ≤ 272535072250795 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13317 ≤ 272535072250794 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13317 : RowArithmetic 13317 (573589277621133874539/500000000000000000000000) (308743534052297878708107/500000000000000000000000) (8333429796727783/1000000000000000000000000) where
  r0 := (650714374247/1000000000000000000)
  k0 := (152543587289249/40000000000000000)
  k6 := (11865811262160451/1000000000000000000)
  q := (326398529408451839/2000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13317]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13317]

theorem width_13318 : mW 13318 = 272606707175440 := by
  have hu : mW 13318 ≤ 272606707175440 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13318 ≤ 272606707175439 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13318 : RowArithmetic 13318 (1147141376765838792669/1000000000000000000000000) (617474495292016164538927/1000000000000000000000000) (2082949374147699/250000000000000000000000) where
  r0 := (650641085973/1000000000000000000)
  k0 := (3813374918821457/1000000000000000000)
  k6 := (11865365773573177/1000000000000000000)
  q := (40801348016946694993/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13318]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13318]

theorem width_13319 : mW 13319 = 272678355548359 := by
  have hu : mW 13319 ≤ 272678355548359 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13319 ≤ 272678355548358 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13319 : RowArithmetic 13319 (143388025957196431003/125000000000000000000000) (617461924384008165554641/1000000000000000000000000) (8330165643250341/1000000000000000000000000) where
  r0 := (130113562291/200000000000000000)
  k0 := (953290045907437/250000000000000000)
  k6 := (2372984067031649/200000000000000000)
  q := (81605759600655639017/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13319]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13319]

theorem width_13320 : mW 13320 = 272750017371067 := by
  have hu : mW 13320 ≤ 272750017371067 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13320 ≤ 272750017371066 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13320 : RowArithmetic 13320 (1147067047914376145729/1000000000000000000000000) (617449355380111135311853/1000000000000000000000000) (4164267118274717/500000000000000000000000) where
  r0 := (650494550689/1000000000000000000)
  k0 := (1906472738324571/500000000000000000)
  k6 := (5932237473453119/500000000000000000)
  q := (163217646104825320141/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13320]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13320]

theorem width_13321 : mW 13321 = 272821692645080 := by
  have hu : mW 13321 ≤ 272821692645080 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13321 ≤ 272821692645079 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13321 : RowArithmetic 13321 (1147029897533163837461/1000000000000000000000000) (308718394139932273617569/500000000000000000000000) (8326903276331129/1000000000000000000000000) where
  r0 := (81302662959/125000000000000000)
  k0 := (953182699468903/250000000000000000)
  k6 := (5932014804403871/500000000000000000)
  q := (40805943194588701971/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13321]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13321]

theorem width_13322 : mW 13322 = 272893381371911 := by
  have hu : mW 13322 ≤ 272893381371911 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13322 ≤ 272893381371910 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13322 : RowArithmetic 13322 (1146992756510849124483/1000000000000000000000000) (617424223082808052369097/1000000000000000000000000) (8325272762438641/1000000000000000000000000) where
  r0 := (50808443/78125000000000)
  k0 := (3812516147302199/1000000000000000000)
  k6 := (370737010026667/31250000000000000)
  q := (32645979844385127599/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13322]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13322]

theorem width_13323 : mW 13323 = 272965083553076 := by
  have hu : mW 13323 ≤ 272965083553076 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13323 ≤ 272965083553075 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13323 : RowArithmetic 13323 (1146955624844345562613/1000000000000000000000000) (12348233195769630093183/20000000000000000000000) (8323642694715161/1000000000000000000000000) where
  r0 := (65027485087/100000000000000000)
  k0 := (476537690615609/125000000000000000)
  k6 := (2965784770758409/250000000000000000)
  q := (81618012717781851173/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13323]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13323]

theorem width_13324 : mW 13324 = 273036799190090 := by
  have hu : mW 13324 ≤ 273036799190090 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13324 ≤ 273036799190089 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13324 : RowArithmetic 13324 (286729625632642197851/250000000000000000000000) (617399098396424761253821/1000000000000000000000000) (8322013073003981/1000000000000000000000000) where
  r0 := (325100822539/500000000000000000)
  k0 := (3812086930736667/1000000000000000000)
  k6 := (11862693895339211/1000000000000000000)
  q := (163242151419294887949/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13324]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13324]

theorem width_13325 : mW 13325 = 273108528284468 := by
  have hu : mW 13325 ≤ 273108528284468 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13325 ≤ 273108528284467 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13325 : RowArithmetic 13325 (573440694783217875441/500000000000000000000000) (154346634726544496488919/250000000000000000000000) (8320383897148461/1000000000000000000000000) where
  r0 := (32506422651/50000000000000000)
  k0 := (3811872364730619/1000000000000000000)
  k6 := (11862248757760663/1000000000000000000)
  q := (81624138586572538481/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13325]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13325]

theorem width_13326 : mW 13326 = 273180270837724 := by
  have hu : mW 13326 ≤ 273180270837724 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13326 ≤ 273180270837723 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13326 : RowArithmetic 13326 (1146844285948865461337/1000000000000000000000000) (617373981317281441807189/1000000000000000000000000) (4159377583496031/500000000000000000000000) where
  r0 := (650055274693/1000000000000000000)
  k0 := (952914456725673/250000000000000000)
  k6 := (1186180367028859/100000000000000000)
  q := (40813600674285036671/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13326]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13326]

theorem width_13327 : mW 13327 = 273252026851374 := by
  have hu : mW 13327 ≤ 273252026851374 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13327 ≤ 273252026851373 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13327 : RowArithmetic 13327 (1146807191674776680423/1000000000000000000000000) (123472285125855107914741/200000000000000000000000) (33268507529513/4000000000000000000000) where
  r0 := (649982110093/1000000000000000000)
  k0 := (952860829311479/250000000000000000)
  k6 := (5930679316456797/500000000000000000)
  q := (163260527991305969561/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13327]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13327]

theorem width_13328 : mW 13328 = 273323796326933 := by
  have hu : mW 13328 ≤ 273323796326933 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13328 ≤ 273323796326932 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13328 : RowArithmetic 13328 (1146770106741090245329/1000000000000000000000000) (617348871841700855189249/1000000000000000000000000) (32482418137307/3906250000000000000000) where
  r0 := (649908959217/1000000000000000000)
  k0 := (952807208939063/250000000000000000)
  k6 := (11860913645626277/1000000000000000000)
  q := (32653330611133682637/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13328]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13328]

theorem width_13329 : mW 13329 = 273395579265916 := by
  have hu : mW 13329 ≤ 273395579265916 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13329 ≤ 273395579265915 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13329 : RowArithmetic 13329 (1146733031144728290887/1000000000000000000000000) (123467263990819610876457/200000000000000000000000) (2078467912288181/250000000000000000000000) where
  r0 := (649835822061/1000000000000000000)
  k0 := (152440575297069/40000000000000000)
  k6 := (2965117177104311/250000000000000000)
  q := (163272777890253340297/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13329]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13329]

theorem width_13330 : mW 13330 = 273467375669839 := by
  have hu : mW 13330 ≤ 273467375669839 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13330 ≤ 273467375669838 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13330 : RowArithmetic 13330 (573347982441306734861/500000000000000000000000) (30866188498300403173297/50000000000000000000000) (51951529376427/6250000000000000000000) where
  r0 := (649762698621/1000000000000000000)
  k0 := (3810799957250361/1000000000000000000)
  k6 := (11860023821277103/1000000000000000000)
  q := (81639451247543304393/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13330]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13330]

theorem width_13331 : mW 13331 = 273539185540217 := by
  have hu : mW 13331 ≤ 273539185540217 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13331 ≤ 273539185540216 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13331 : RowArithmetic 13331 (1146658907951670510857/1000000000000000000000000) (308655610938485931706379/500000000000000000000000) (8310618196221153/1000000000000000000000000) where
  r0 := (324844794447/500000000000000000)
  k0 := (1905292780111557/500000000000000000)
  k6 := (741223686512279/62500000000000000)
  q := (163285026870194071693/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13331]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13331]

theorem width_13332 : mW 13332 = 273611008878564 := by
  have hu : mW 13332 ≤ 273611008878564 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13332 ≤ 273611008878563 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13332 : RowArithmetic 13332 (71663866271801638581/62500000000000000000000) (617298675686530657672819/1000000000000000000000000) (4154496068487547/500000000000000000000000) where
  r0 := (649616492877/1000000000000000000)
  k0 := (3810371191340937/1000000000000000000)
  k6 := (592956709858297/50000000000000000)
  q := (16329115101560157721/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13332]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13332]

theorem width_13333 : mW 13333 = 273682845686398 := by
  have hu : mW 13333 ≤ 273682845686398 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13333 ≤ 273682845686397 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13333 : RowArithmetic 13333 (1146584822071005573027/1000000000000000000000000) (617286131394225734929279/1000000000000000000000000) (8307366522333963/1000000000000000000000000) where
  r0 := (162385852641/250000000000000000)
  k0 := (476269606323873/125000000000000000)
  k6 := (11858689460176147/1000000000000000000)
  q := (4082431873283374217/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13333]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13333]

theorem width_13334 : mW 13334 = 273754695965232 := by
  have hu : mW 13334 ≤ 273754695965232 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13334 ≤ 273754695965231 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13334 : RowArithmetic 13334 (573273896557569374567/500000000000000000000000) (617273588999598564131893/1000000000000000000000000) (41528706760709/5000000000000000000000) where
  r0 := (324735170977/500000000000000000)
  k0 := (952485634493767/250000000000000000)
  k6 := (11858244773217701/1000000000000000000)
  q := (32660679723484016921/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13334]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13334]

theorem width_13335 : mW 13335 = 273826559716583 := by
  have hu : mW 13335 ≤ 273826559716583 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13335 ≤ 273826559716582 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13335 : RowArithmetic 13335 (573255386739077048817/500000000000000000000000) (77157631062773852984889/125000000000000000000000) (8304116626242591/1000000000000000000000000) where
  r0 := (649397287043/1000000000000000000)
  k0 := (1904864126743103/500000000000000000)
  k6 := (1482225017035153/125000000000000000)
  q := (163309522073882758639/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13335]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13335]

theorem width_13336 : mW 13336 = 273898436941966 := by
  have hu : mW 13336 ≤ 273898436941966 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13336 ≤ 273898436941965 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13336 : RowArithmetic 13336 (45858950526279312807/40000000000000000000000) (617248509901544292380293/1000000000000000000000000) (2075623086120113/250000000000000000000000) where
  r0 := (324662122913/500000000000000000)
  k0 := (152380559884579/40000000000000000)
  k6 := (11857355549357337/1000000000000000000)
  q := (163315645300748819593/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13336]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13336]

theorem width_13337 : mW 13337 = 273970327642898 := by
  have hu : mW 13337 ≤ 273970327642898 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13337 ≤ 273970327642897 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13337 : RowArithmetic 13337 (286609190537138964223/250000000000000000000000) (12344719463944016553017/20000000000000000000000) (4150434253349753/500000000000000000000000) where
  r0 := (6492512183/10000000000000000)
  k0 := (190464988442791/50000000000000000)
  k6 := (5928455506218333/500000000000000000)
  q := (81660884149022045719/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13337]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13337]

theorem width_13338 : mW 13338 = 274042231820893 := by
  have hu : mW 13338 ≤ 274042231820893 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13338 ≤ 274042231820892 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13338 : RowArithmetic 13338 (1146399770449807771199/1000000000000000000000000) (123444687677740513784679/200000000000000000000000) (4149622556372019/500000000000000000000000) where
  r0 := (324589102231/500000000000000000)
  k0 := (3809085568706183/1000000000000000000)
  k6 := (5928233262754919/500000000000000000)
  q := (20415986383224299163/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13338]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13338]

theorem width_13339 : mW 13339 = 274114149477467 := by
  have hu : mW 13339 ≤ 274114149477467 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13339 ≤ 274114149477466 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13339 : RowArithmetic 13339 (1146362788057672863593/1000000000000000000000000) (308605452737795866219047/500000000000000000000000) (8297622162458337/1000000000000000000000000) where
  r0 := (649105204307/1000000000000000000)
  k0 := (952217849163909/250000000000000000)
  k6 := (11856022088567483/1000000000000000000)
  q := (163334013604025539479/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13339]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13339]

theorem width_13340 : mW 13340 = 274186080614137 := by
  have hu : mW 13340 ≤ 274186080614137 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13340 ≤ 274186080614136 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13340 : RowArithmetic 13340 (1146325814969085950091/1000000000000000000000000) (617198374457410702207543/1000000000000000000000000) (8295999655686733/1000000000000000000000000) where
  r0 := (324516108917/500000000000000000)
  k0 := (761731450541197/200000000000000000)
  k6 := (11855577701600233/1000000000000000000)
  q := (81670067956381669709/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13340]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13340]

theorem width_13341 : mW 13341 = 274258025232418 := by
  have hu : mW 13341 ≤ 274258025232418 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13341 ≤ 274258025232417 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13341 : RowArithmetic 13341 (573144425590492344711/500000000000000000000000) (617185845333702050424973/1000000000000000000000000) (8294377592273683/1000000000000000000000000) where
  r0 := (648959245037/1000000000000000000)
  k0 := (1904221568422183/500000000000000000)
  k6 := (2963783341149681/250000000000000000)
  q := (81673128996016798867/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13341]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13341]

theorem width_13342 : mW 13342 = 274329983333826 := by
  have hu : mW 13342 ≤ 274329983333826 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13342 ≤ 274329983333825 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13342 : RowArithmetic 13342 (1146251896690307253753/1000000000000000000000000) (154293329526002103582751/250000000000000000000000) (2073188993015921/250000000000000000000000) where
  r0 := (648886285913/1000000000000000000)
  k0 := (476028631133339/125000000000000000)
  k6 := (11854689077553593/1000000000000000000)
  q := (163352379841862114207/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13342]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13342]

theorem width_13343 : mW 13343 = 274401954919877 := by
  have hu : mW 13343 ≤ 274401954919877 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13343 ≤ 274401954919876 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13343 : RowArithmetic 13343 (1146214951493993104403/1000000000000000000000000) (617160792767872650728673/1000000000000000000000000) (82911347949013/10000000000000000000000) where
  r0 := (648813340459/1000000000000000000)
  k0 := (952003747342239/250000000000000000)
  k6 := (11854244840455479/1000000000000000000)
  q := (20419812682784335473/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13343]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13343]

theorem width_13344 : mW 13344 = 274473939992087 := by
  have hu : mW 13344 ≤ 274473939992087 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13344 ≤ 274473939992086 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13344 : RowArithmetic 13344 (143272251948622873893/125000000000000000000000) (154287067331209439219937/250000000000000000000000) (8289514060631163/1000000000000000000000000) where
  r0 := (648740408671/1000000000000000000)
  k0 := (118993779929503/31250000000000000)
  k6 := (474152026131801/40000000000000000)
  q := (163364622853297096577/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13344]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13344]

theorem width_13345 : mW 13345 = 274545938551973 := by
  have hu : mW 13345 ≤ 274545938551973 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13345 ≤ 274545938551972 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13345 : RowArithmetic 13345 (71633818060763636091/62500000000000000000000) (617135747774446863277907/1000000000000000000000000) (8287893769097943/1000000000000000000000000) where
  r0 := (324333745273/500000000000000000)
  k0 := (3807586954188059/1000000000000000000)
  k6 := (2963339129015719/250000000000000000)
  q := (163370744014955137867/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13345]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13345]

theorem width_13346 : mW 13346 = 274617950601050 := by
  have hu : mW 13346 ≤ 274617950601050 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13346 ≤ 274617950601049 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13346 : RowArithmetic 13346 (1146104171640642762637/1000000000000000000000000) (617123228116243272259463/1000000000000000000000000) (8286273920146441/1000000000000000000000000) where
  r0 := (4053716163/6250000000000000)
  k0 := (47592162233673/12500000000000000)
  k6 := (5926456214374839/500000000000000000)
  q := (32675372989454917621/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13346]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13346]

theorem width_13347 : mW 13347 = 274689976140835 := by
  have hu : mW 13347 ≤ 274689976140835 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13347 ≤ 274689976140834 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13347 : RowArithmetic 13347 (4584269054364802337/4000000000000000000000) (308555355174885205634861/500000000000000000000000) (8284654513621461/1000000000000000000000000) where
  r0 := (648521695269/1000000000000000000)
  k0 := (951789757813607/250000000000000000)
  k6 := (11852468391346081/1000000000000000000)
  q := (163382985650281222911/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13347]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13347]

theorem width_13348 : mW 13348 = 274762015172844 := by
  have hu : mW 13348 ≤ 274762015172844 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13348 ≤ 274762015172843 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13348 : RowArithmetic 13348 (573015182410418769947/500000000000000000000000) (3856863715466074197929/6250000000000000000000) (8283035549367911/1000000000000000000000000) where
  r0 := (648448818109/1000000000000000000)
  k0 := (3806945111862811/1000000000000000000)
  k6 := (5926012201921369/500000000000000000)
  q := (4084727653100020327/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13348]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13348]

theorem width_13349 : mW 13349 = 274834067698593 := by
  have hu : mW 13349 ≤ 274834067698593 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13349 ≤ 274834067698592 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13349 : RowArithmetic 13349 (572996737663250406063/500000000000000000000000) (617085680490191396884843/1000000000000000000000000) (4140708513615381/500000000000000000000000) where
  r0 := (324187977299/500000000000000000)
  k0 := (475841402564731/125000000000000000)
  k6 := (5925790233115151/500000000000000000)
  q := (81697613184229562289/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13349]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13349]

theorem width_13350 : mW 13350 = 274906133719599 := by
  have hu : mW 13350 ≤ 274906133719599 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13350 ≤ 274906133719598 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13350 : RowArithmetic 13350 (1145956595105138095401/1000000000000000000000000) (617073168396172908668917/1000000000000000000000000) (331191957882201/40000000000000000000000) where
  r0 := (648303104731/1000000000000000000)
  k0 := (1903258678604793/500000000000000000)
  k6 := (11851136578499431/1000000000000000000)
  q := (163401346383681918547/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13350]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13350]

theorem width_13351 : mW 13351 = 274978213237378 := by
  have hu : mW 13351 ≤ 274978213237378 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13351 ≤ 274978213237377 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13351 : RowArithmetic 13351 (1145919724153699141107/1000000000000000000000000) (308530329096030217946051/500000000000000000000000) (8278181308685811/1000000000000000000000000) where
  r0 := (324115134253/500000000000000000)
  k0 := (3806303521936881/1000000000000000000)
  k6 := (740668296290049/62500000000000000)
  q := (32681493233938990261/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13351]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13351]

theorem width_13352 : mW 13352 = 275050306253447 := by
  have hu : mW 13352 ≤ 275050306253447 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13352 ≤ 275050306253446 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13352 : RowArithmetic 13352 (286470715617283552953/250000000000000000000000) (77131018734674775264687/125000000000000000000000) (1655312822393653/200000000000000000000000) where
  r0 := (324078722959/500000000000000000)
  k0 := (237880607168111/62500000000000000)
  k6 := (370320279770157/31250000000000000)
  q := (32682717145304794869/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13352]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13352]

theorem width_13353 : mW 13353 = 275122412769323 := by
  have hu : mW 13353 ≤ 275122412769323 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13353 ≤ 275122412769322 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13353 : RowArithmetic 13353 (1432307512560493567/1250000000000000000000) (123407128690346096015873/200000000000000000000000) (8274947356747603/1000000000000000000000000) where
  r0 := (162021159241/250000000000000000)
  k0 := (3805875935464187/1000000000000000000)
  k6 := (11849805214502813/1000000000000000000)
  q := (163419705054194734341/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13353]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13353]

theorem width_13354 : mW 13354 = 275194532786521 := by
  have hu : mW 13354 ≤ 275194532786521 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13354 ≤ 275194532786520 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13354 : RowArithmetic 13354 (286452291722108859347/250000000000000000000000) (123404627782920360830659/200000000000000000000000) (517083190179323/62500000000000000000000) where
  r0 := (16200296041/25000000000000000)
  k0 := (3805662184253091/1000000000000000000)
  k6 := (592468076310241/50000000000000000)
  q := (81712912076366486573/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13354]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13354]

theorem width_13355 : mW 13355 = 275266666306559 := by
  have hu : mW 13355 ≤ 275266666306559 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13355 ≤ 275266666306558 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13355 : RowArithmetic 13355 (572886166493104650753/500000000000000000000000) (617010636265556868241069/1000000000000000000000000) (8271715170178281/1000000000000000000000000) where
  r0 := (323969529971/500000000000000000)
  k0 := (190272423052473/50000000000000000)
  k6 := (11848917887741713/1000000000000000000)
  q := (81715971511082213897/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13355]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13355]

theorem width_13356 : mW 13356 = 275338813330954 := by
  have hu : mW 13356 ≤ 275338813330954 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13356 ≤ 275338813330953 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13356 : RowArithmetic 13356 (71608469271166989837/62500000000000000000000) (616998135504140453616073/1000000000000000000000000) (8270099738520359/1000000000000000000000000) where
  r0 := (161966572967/250000000000000000)
  k0 := (1902617382926071/500000000000000000)
  k6 := (2962118574776041/250000000000000000)
  q := (326876123325029661/2000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13356]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13356]

theorem width_13357 : mW 13357 = 275410973861222 := by
  have hu : mW 13357 ≤ 275410973861222 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13357 ≤ 275410973861221 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13357 : RowArithmetic 13357 (114569869294278048721/100000000000000000000000) (4820200286171073695219/7812500000000000000000) (206712118693523/25000000000000000000000) where
  r0 := (323896768707/500000000000000000)
  k0 := (3805021098654107/1000000000000000000)
  k6 := (11848030760282847/1000000000000000000)
  q := (163444180073809908663/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13357]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13357]

theorem width_13358 : mW 13358 = 275483147898880 := by
  have hu : mW 13358 ≤ 275483147898880 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13358 ≤ 275483147898879 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13358 : RowArithmetic 13358 (1145661886795493202153/1000000000000000000000000) (123394627928474594962327/200000000000000000000000) (8266870197685517/1000000000000000000000000) where
  r0 := (25908831863/40000000000000000)
  k0 := (1902403729722693/500000000000000000)
  k6 := (5923793635634219/500000000000000000)
  q := (163450298256075384869/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13358]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13358]

theorem width_13359 : mW 13359 = 275555335445444 := by
  have hu : mW 13359 ≤ 275555335445444 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13359 ≤ 275555335445443 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13359 : RowArithmetic 13359 (1790039202959015597/1562500000000000000000) (616960644541112345064237/1000000000000000000000000) (4132628044099901/500000000000000000000000) where
  r0 := (647648069349/1000000000000000000)
  k0 := (3804593848224821/1000000000000000000)
  k6 := (11847143832051617/1000000000000000000)
  q := (163456416209336976887/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13359]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13359]

theorem width_13360 : mW 13360 = 275627536502433 := by
  have hu : mW 13360 ≤ 275627536502433 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13360 ≤ 275627536502432 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13360 : RowArithmetic 13360 (1145588302234569797177/1000000000000000000000000) (154237037831415216386549/250000000000000000000000) (1652728483825881/200000000000000000000000) where
  r0 := (161893838933/250000000000000000)
  k0 := (3804380264985377/1000000000000000000)
  k6 := (2369340088524613/200000000000000000)
  q := (81731266966810198837/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13360]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13360]

theorem width_13361 : mW 13361 = 275699751071363 := by
  have hu : mW 13361 ≤ 275699751071363 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13361 ≤ 275699751071362 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13361 : RowArithmetic 13361 (1145551523814855204237/1000000000000000000000000) (616935659995564166474527/1000000000000000000000000) (8262029190320113/1000000000000000000000000) where
  r0 := (16187566393/25000000000000000)
  k0 := (760833341944003/200000000000000000)
  k6 := (2369251420594693/200000000000000000)
  q := (163468651428951355377/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13361]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13361]

theorem width_13362 : mW 13362 = 275771979153751 := by
  have hu : mW 13362 ≤ 275771979153751 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13362 ≤ 275771979153750 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13362 : RowArithmetic 13362 (286378688657897316911/250000000000000000000000) (616923170550367921955173/1000000000000000000000000) (8260416401617751/1000000000000000000000000) where
  r0 := (64742996931/100000000000000000)
  k0 := (1901976591212317/500000000000000000)
  k6 := (2369162762618701/200000000000000000)
  q := (163474768695355553331/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13362]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13362]

theorem width_13363 : mW 13363 = 275844220751114 := by
  have hu : mW 13363 ≤ 275844220751114 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13363 ≤ 275844220751113 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13363 : RowArithmetic 13363 (286369498670434082087/250000000000000000000000) (123382136597923584905273/200000000000000000000000) (8258804052868211/1000000000000000000000000) where
  r0 := (323678648249/500000000000000000)
  k0 := (1901869841546097/500000000000000000)
  k6 := (11845370572973873/1000000000000000000)
  q := (10217555358303668129/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13363]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13363]

theorem width_13364 : mW 13364 = 275916475864970 := by
  have hu : mW 13364 ≤ 275916475864970 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13364 ≤ 275916475864969 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13364 : RowArithmetic 13364 (286360310990565308881/250000000000000000000000) (61689819731286024300403/100000000000000000000000) (516074508994839/62500000000000000000000) where
  r0 := (647284637281/1000000000000000000)
  k0 := (950881552929647/250000000000000000)
  k6 := (11844927382605259/1000000000000000000)
  q := (163487002541486459293/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13364]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13364]

theorem width_13365 : mW 13365 = 275988744496835 := by
  have hu : mW 13365 ≤ 275988744496835 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13365 ≤ 275988744496834 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13365 : RowArithmetic 13365 (1145404502470131649491/1000000000000000000000000) (616885713519641004194547/1000000000000000000000000) (4127790337305723/500000000000000000000000) where
  r0 := (129442398331/200000000000000000)
  k0 := (950828192074193/250000000000000000)
  k6 := (5922242120989179/500000000000000000)
  q := (163493119121264549933/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13365]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13365]

theorem width_13366 : mW 13366 = 276061026648227 := by
  have hu : mW 13366 ≤ 276061026648227 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13366 ≤ 276061026648226 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13366 : RowArithmetic 13366 (7158548563764468561/6250000000000000000000) (308436615804753250586849/500000000000000000000000) (4126984822398171/500000000000000000000000) where
  r0 := (5055776247/7812500000000000)
  k0 := (1901549676409849/500000000000000000)
  k6 := (5922020575541933/500000000000000000)
  q := (163499235472218646091/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13366]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13366]

theorem width_13367 : mW 13367 = 276133322320664 := by
  have hu : mW 13367 ≤ 276133322320664 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13367 ≤ 276133322320663 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13367 : RowArithmetic 13367 (4473949402952265121/3906250000000000000000) (123372150316400634604509/200000000000000000000000) (4126179527159123/500000000000000000000000) where
  r0 := (323533370581/500000000000000000)
  k0 := (1901442982643097/500000000000000000)
  k6 := (74022488186953/6250000000000000)
  q := (16350535159437442707/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13367]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13367]

theorem width_13368 : mW 13368 = 276205631515662 := by
  have hu : mW 13368 ≤ 276205631515662 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13368 ≤ 276205631515661 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13368 : RowArithmetic 13368 (22905886666549956697/20000000000000000000000) (616848273436677630310059/1000000000000000000000000) (1031343612877927/125000000000000000000000) where
  r0 := (646994136287/1000000000000000000)
  k0 := (3802672605683331/1000000000000000000)
  k6 := (11843155118454903/1000000000000000000)
  q := (163511467487757567371/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13368]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13368]

theorem width_13369 : mW 13369 = 276277954234740 := by
  have hu : mW 13369 ≤ 276277954234740 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13369 ≤ 276277954234739 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13369 : RowArithmetic 13369 (14315720358930491453/12500000000000000000000) (616835797173076613222687/1000000000000000000000000) (824913919075809/100000000000000000000000) where
  r0 := (64692154499/100000000000000000)
  k0 := (3802459274012873/1000000000000000000)
  k6 := (11842712176701837/1000000000000000000)
  q := (81758791576196868347/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13369]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13369]

theorem width_13370 : mW 13370 = 276350290479415 := by
  have hu : mW 13370 ≤ 276350290479415 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13370 ≤ 276350290479414 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13370 : RowArithmetic 13370 (229044186662715515137/200000000000000000000000) (154205830697686756214989/250000000000000000000000) (4123764958684317/500000000000000000000000) where
  r0 := (323424483633/500000000000000000)
  k0 := (152089838810593/40000000000000000)
  k6 := (11842269284643989/1000000000000000000)
  q := (81761849294154299969/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13370]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13370]

theorem width_13371 : mW 13371 = 276422640251204 := by
  have hu : mW 13371 ≤ 276422640251204 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13371 ≤ 276422640251203 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13371 : RowArithmetic 13371 (572592123560943572381/500000000000000000000000) (154202712572308980796697/250000000000000000000000) (8245921082701477/1000000000000000000000000) where
  r0 := (646776403111/1000000000000000000)
  k0 := (3802032694432131/1000000000000000000)
  k6 := (5920913221136033/500000000000000000)
  q := (40882453448881954301/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13371]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13371]

theorem width_13372 : mW 13372 = 276495003551625 := by
  have hu : mW 13372 ≤ 276495003551625 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13372 ≤ 276495003551624 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13372 : RowArithmetic 13372 (17892930783380360319/15625000000000000000000) (616798379668090494373077/1000000000000000000000000) (8244312686603091/1000000000000000000000000) where
  r0 := (646703852523/1000000000000000000)
  k0 := (380181944651361/100000000000000000)
  k6 := (5920691824788389/500000000000000000)
  q := (32707185754815408759/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13372]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13372]

theorem width_13373 : mW 13373 = 276567380382196 := by
  have hu : mW 13373 ≤ 276567380382196 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13373 ≤ 276567380382195 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13373 : RowArithmetic 13373 (229022180470784326117/200000000000000000000000) (12335718218537161264633/20000000000000000000000) (8242704728920011/1000000000000000000000000) where
  r0 := (646631315497/1000000000000000000)
  k0 := (3801606226499261/1000000000000000000)
  k6 := (296023522663721/25000000000000000)
  q := (163542043523981930217/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13373]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13373]

theorem width_13374 : mW 13374 = 276639770744435 := by
  have hu : mW 13374 ≤ 276639770744435 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13374 ≤ 276639770744434 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13374 : RowArithmetic 13374 (286268560942900108377/250000000000000000000000) (154193361016271533017039/250000000000000000000000) (8241097209498841/1000000000000000000000000) where
  r0 := (646558792031/1000000000000000000)
  k0 := (3801393034387901/1000000000000000000)
  k6 := (11840498213178967/1000000000000000000)
  q := (81774079022634061091/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13374]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13374]

theorem width_13375 : mW 13375 = 276712174639859 := by
  have hu : mW 13375 ≤ 276712174639859 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13375 ≤ 276712174639858 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13375 : RowArithmetic 13375 (1145037594386359081013/1000000000000000000000000) (616760979082322354976697/1000000000000000000000000) (8239490128186283/1000000000000000000000000) where
  r0 := (16162157053/25000000000000000)
  k0 := (152047194806781/40000000000000000)
  k6 := (2960013892364469/250000000000000000)
  q := (2555535505280644697/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13375]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13375]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 13301 then ⟨(1147774687460822008137/1000000000000000000000000), (617688492504094576313473/1000000000000000000000000), (8359607491598489/1000000000000000000000000)⟩ else
  if n = 13302 then ⟨(1147737358672637057621/1000000000000000000000000), (61767588915559544081067/100000000000000000000000), (2089492005328403/250000000000000000000000)⟩ else
  if n = 13303 then ⟨(143462504912776694323/125000000000000000000000), (617663287719059210378931/1000000000000000000000000), (1044541125043251/125000000000000000000000)⟩ else
  if n = 13304 then ⟨(14345784116830532131/12500000000000000000000), (61765068819402276978201/100000000000000000000000), (4177345214268823/500000000000000000000000)⟩ else
  if n = 13305 then ⟨(1147625428802216488711/1000000000000000000000000), (154409522645005783413571/250000000000000000000000), (8353052305730563/1000000000000000000000000)⟩ else
  if n = 13306 then ⟨(1147588137666427429171/1000000000000000000000000), (38601593429787347563421/62500000000000000000000), (2087853657941701/250000000000000000000000)⟩ else
  if n = 13307 then ⟨(573775427967984806033/500000000000000000000000), (617612901083283384072903/1000000000000000000000000), (4174888703244257/500000000000000000000000)⟩ else
  if n = 13308 then ⟨(286878395901934838869/250000000000000000000000), (154400077299904523276511/250000000000000000000000), (8348140629737939/1000000000000000000000000)⟩ else
  if n = 13309 then ⟨(143434540084829089237/125000000000000000000000), (308793859612569678810103/500000000000000000000000), (8346504301357333/1000000000000000000000000)⟩ else
  if n = 13310 then ⟨(229487813429109567791/200000000000000000000000), (617575131159385005133341/1000000000000000000000000), (8344868421189049/1000000000000000000000000)⟩ else
  if n = 13311 then ⟨(1147401823005384191329/1000000000000000000000000), (7719531812523662470737/12500000000000000000000), (834323298907551/100000000000000000000000)⟩ else
  if n = 13312 then ⟨(45894583530201701601/40000000000000000000000), (15438749018805036342069/25000000000000000000000), (834159800485921/100000000000000000000000)⟩ else
  if n = 13313 then ⟨(143415920361428022089/125000000000000000000000), (308768689204924328177713/500000000000000000000000), (8339963468382679/1000000000000000000000000)⟩ else
  if n = 13314 then ⟨(1147290146911432485959/1000000000000000000000000), (61752479797437301353641/100000000000000000000000), (2084582344872137/250000000000000000000000)⟩ else
  if n = 13315 then ⟨(71703308769498210891/62500000000000000000000), (38594513715332072994467/62500000000000000000000), (8336695738019487/1000000000000000000000000)⟩ else
  if n = 13316 then ⟨(35850491971560863213/31250000000000000000000), (123499928564441551402721/200000000000000000000000), (1041882817977287/125000000000000000000000)⟩ else
  if n = 13317 then ⟨(573589277621133874539/500000000000000000000000), (308743534052297878708107/500000000000000000000000), (8333429796727783/1000000000000000000000000)⟩ else
  if n = 13318 then ⟨(1147141376765838792669/1000000000000000000000000), (617474495292016164538927/1000000000000000000000000), (2082949374147699/250000000000000000000000)⟩ else
  if n = 13319 then ⟨(143388025957196431003/125000000000000000000000), (617461924384008165554641/1000000000000000000000000), (8330165643250341/1000000000000000000000000)⟩ else
  if n = 13320 then ⟨(1147067047914376145729/1000000000000000000000000), (617449355380111135311853/1000000000000000000000000), (4164267118274717/500000000000000000000000)⟩ else
  if n = 13321 then ⟨(1147029897533163837461/1000000000000000000000000), (308718394139932273617569/500000000000000000000000), (8326903276331129/1000000000000000000000000)⟩ else
  if n = 13322 then ⟨(1146992756510849124483/1000000000000000000000000), (617424223082808052369097/1000000000000000000000000), (8325272762438641/1000000000000000000000000)⟩ else
  if n = 13323 then ⟨(1146955624844345562613/1000000000000000000000000), (12348233195769630093183/20000000000000000000000), (8323642694715161/1000000000000000000000000)⟩ else
  if n = 13324 then ⟨(286729625632642197851/250000000000000000000000), (617399098396424761253821/1000000000000000000000000), (8322013073003981/1000000000000000000000000)⟩ else
  if n = 13325 then ⟨(573440694783217875441/500000000000000000000000), (154346634726544496488919/250000000000000000000000), (8320383897148461/1000000000000000000000000)⟩ else
  if n = 13326 then ⟨(1146844285948865461337/1000000000000000000000000), (617373981317281441807189/1000000000000000000000000), (4159377583496031/500000000000000000000000)⟩ else
  if n = 13327 then ⟨(1146807191674776680423/1000000000000000000000000), (123472285125855107914741/200000000000000000000000), (33268507529513/4000000000000000000000)⟩ else
  if n = 13328 then ⟨(1146770106741090245329/1000000000000000000000000), (617348871841700855189249/1000000000000000000000000), (32482418137307/3906250000000000000000)⟩ else
  if n = 13329 then ⟨(1146733031144728290887/1000000000000000000000000), (123467263990819610876457/200000000000000000000000), (2078467912288181/250000000000000000000000)⟩ else
  if n = 13330 then ⟨(573347982441306734861/500000000000000000000000), (30866188498300403173297/50000000000000000000000), (51951529376427/6250000000000000000000)⟩ else
  if n = 13331 then ⟨(1146658907951670510857/1000000000000000000000000), (308655610938485931706379/500000000000000000000000), (8310618196221153/1000000000000000000000000)⟩ else
  if n = 13332 then ⟨(71663866271801638581/62500000000000000000000), (617298675686530657672819/1000000000000000000000000), (4154496068487547/500000000000000000000000)⟩ else
  if n = 13333 then ⟨(1146584822071005573027/1000000000000000000000000), (617286131394225734929279/1000000000000000000000000), (8307366522333963/1000000000000000000000000)⟩ else
  if n = 13334 then ⟨(573273896557569374567/500000000000000000000000), (617273588999598564131893/1000000000000000000000000), (41528706760709/5000000000000000000000)⟩ else
  if n = 13335 then ⟨(573255386739077048817/500000000000000000000000), (77157631062773852984889/125000000000000000000000), (8304116626242591/1000000000000000000000000)⟩ else
  if n = 13336 then ⟨(45858950526279312807/40000000000000000000000), (617248509901544292380293/1000000000000000000000000), (2075623086120113/250000000000000000000000)⟩ else
  if n = 13337 then ⟨(286609190537138964223/250000000000000000000000), (12344719463944016553017/20000000000000000000000), (4150434253349753/500000000000000000000000)⟩ else
  if n = 13338 then ⟨(1146399770449807771199/1000000000000000000000000), (123444687677740513784679/200000000000000000000000), (4149622556372019/500000000000000000000000)⟩ else
  if n = 13339 then ⟨(1146362788057672863593/1000000000000000000000000), (308605452737795866219047/500000000000000000000000), (8297622162458337/1000000000000000000000000)⟩ else
  if n = 13340 then ⟨(1146325814969085950091/1000000000000000000000000), (617198374457410702207543/1000000000000000000000000), (8295999655686733/1000000000000000000000000)⟩ else
  if n = 13341 then ⟨(573144425590492344711/500000000000000000000000), (617185845333702050424973/1000000000000000000000000), (8294377592273683/1000000000000000000000000)⟩ else
  if n = 13342 then ⟨(1146251896690307253753/1000000000000000000000000), (154293329526002103582751/250000000000000000000000), (2073188993015921/250000000000000000000000)⟩ else
  if n = 13343 then ⟨(1146214951493993104403/1000000000000000000000000), (617160792767872650728673/1000000000000000000000000), (82911347949013/10000000000000000000000)⟩ else
  if n = 13344 then ⟨(143272251948622873893/125000000000000000000000), (154287067331209439219937/250000000000000000000000), (8289514060631163/1000000000000000000000000)⟩ else
  if n = 13345 then ⟨(71633818060763636091/62500000000000000000000), (617135747774446863277907/1000000000000000000000000), (8287893769097943/1000000000000000000000000)⟩ else
  if n = 13346 then ⟨(1146104171640642762637/1000000000000000000000000), (617123228116243272259463/1000000000000000000000000), (8286273920146441/1000000000000000000000000)⟩ else
  if n = 13347 then ⟨(4584269054364802337/4000000000000000000000), (308555355174885205634861/500000000000000000000000), (8284654513621461/1000000000000000000000000)⟩ else
  if n = 13348 then ⟨(573015182410418769947/500000000000000000000000), (3856863715466074197929/6250000000000000000000), (8283035549367911/1000000000000000000000000)⟩ else
  if n = 13349 then ⟨(572996737663250406063/500000000000000000000000), (617085680490191396884843/1000000000000000000000000), (4140708513615381/500000000000000000000000)⟩ else
  if n = 13350 then ⟨(1145956595105138095401/1000000000000000000000000), (617073168396172908668917/1000000000000000000000000), (331191957882201/40000000000000000000000)⟩ else
  if n = 13351 then ⟨(1145919724153699141107/1000000000000000000000000), (308530329096030217946051/500000000000000000000000), (8278181308685811/1000000000000000000000000)⟩ else
  if n = 13352 then ⟨(286470715617283552953/250000000000000000000000), (77131018734674775264687/125000000000000000000000), (1655312822393653/200000000000000000000000)⟩ else
  if n = 13353 then ⟨(1432307512560493567/1250000000000000000000), (123407128690346096015873/200000000000000000000000), (8274947356747603/1000000000000000000000000)⟩ else
  if n = 13354 then ⟨(286452291722108859347/250000000000000000000000), (123404627782920360830659/200000000000000000000000), (517083190179323/62500000000000000000000)⟩ else
  if n = 13355 then ⟨(572886166493104650753/500000000000000000000000), (617010636265556868241069/1000000000000000000000000), (8271715170178281/1000000000000000000000000)⟩ else
  if n = 13356 then ⟨(71608469271166989837/62500000000000000000000), (616998135504140453616073/1000000000000000000000000), (8270099738520359/1000000000000000000000000)⟩ else
  if n = 13357 then ⟨(114569869294278048721/100000000000000000000000), (4820200286171073695219/7812500000000000000000), (206712118693523/25000000000000000000000)⟩ else
  if n = 13358 then ⟨(1145661886795493202153/1000000000000000000000000), (123394627928474594962327/200000000000000000000000), (8266870197685517/1000000000000000000000000)⟩ else
  if n = 13359 then ⟨(1790039202959015597/1562500000000000000000), (616960644541112345064237/1000000000000000000000000), (4132628044099901/500000000000000000000000)⟩ else
  if n = 13360 then ⟨(1145588302234569797177/1000000000000000000000000), (154237037831415216386549/250000000000000000000000), (1652728483825881/200000000000000000000000)⟩ else
  if n = 13361 then ⟨(1145551523814855204237/1000000000000000000000000), (616935659995564166474527/1000000000000000000000000), (8262029190320113/1000000000000000000000000)⟩ else
  if n = 13362 then ⟨(286378688657897316911/250000000000000000000000), (616923170550367921955173/1000000000000000000000000), (8260416401617751/1000000000000000000000000)⟩ else
  if n = 13363 then ⟨(286369498670434082087/250000000000000000000000), (123382136597923584905273/200000000000000000000000), (8258804052868211/1000000000000000000000000)⟩ else
  if n = 13364 then ⟨(286360310990565308881/250000000000000000000000), (61689819731286024300403/100000000000000000000000), (516074508994839/62500000000000000000000)⟩ else
  if n = 13365 then ⟨(1145404502470131649491/1000000000000000000000000), (616885713519641004194547/1000000000000000000000000), (4127790337305723/500000000000000000000000)⟩ else
  if n = 13366 then ⟨(7158548563764468561/6250000000000000000000), (308436615804753250586849/500000000000000000000000), (4126984822398171/500000000000000000000000)⟩ else
  if n = 13367 then ⟨(4473949402952265121/3906250000000000000000), (123372150316400634604509/200000000000000000000000), (4126179527159123/500000000000000000000000)⟩ else
  if n = 13368 then ⟨(22905886666549956697/20000000000000000000000), (616848273436677630310059/1000000000000000000000000), (1031343612877927/125000000000000000000000)⟩ else
  if n = 13369 then ⟨(14315720358930491453/12500000000000000000000), (616835797173076613222687/1000000000000000000000000), (824913919075809/100000000000000000000000)⟩ else
  if n = 13370 then ⟨(229044186662715515137/200000000000000000000000), (154205830697686756214989/250000000000000000000000), (4123764958684317/500000000000000000000000)⟩ else
  if n = 13371 then ⟨(572592123560943572381/500000000000000000000000), (154202712572308980796697/250000000000000000000000), (8245921082701477/1000000000000000000000000)⟩ else
  if n = 13372 then ⟨(17892930783380360319/15625000000000000000000), (616798379668090494373077/1000000000000000000000000), (8244312686603091/1000000000000000000000000)⟩ else
  if n = 13373 then ⟨(229022180470784326117/200000000000000000000000), (12335718218537161264633/20000000000000000000000), (8242704728920011/1000000000000000000000000)⟩ else
  if n = 13374 then ⟨(286268560942900108377/250000000000000000000000), (154193361016271533017039/250000000000000000000000), (8241097209498841/1000000000000000000000000)⟩ else
  ⟨(1145037594386359081013/1000000000000000000000000), (616760979082322354976697/1000000000000000000000000), (8239490128186283/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 13301 ≤ n) (hb : n ≤ 13375) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_13301
  · exact row_13302
  · exact row_13303
  · exact row_13304
  · exact row_13305
  · exact row_13306
  · exact row_13307
  · exact row_13308
  · exact row_13309
  · exact row_13310
  · exact row_13311
  · exact row_13312
  · exact row_13313
  · exact row_13314
  · exact row_13315
  · exact row_13316
  · exact row_13317
  · exact row_13318
  · exact row_13319
  · exact row_13320
  · exact row_13321
  · exact row_13322
  · exact row_13323
  · exact row_13324
  · exact row_13325
  · exact row_13326
  · exact row_13327
  · exact row_13328
  · exact row_13329
  · exact row_13330
  · exact row_13331
  · exact row_13332
  · exact row_13333
  · exact row_13334
  · exact row_13335
  · exact row_13336
  · exact row_13337
  · exact row_13338
  · exact row_13339
  · exact row_13340
  · exact row_13341
  · exact row_13342
  · exact row_13343
  · exact row_13344
  · exact row_13345
  · exact row_13346
  · exact row_13347
  · exact row_13348
  · exact row_13349
  · exact row_13350
  · exact row_13351
  · exact row_13352
  · exact row_13353
  · exact row_13354
  · exact row_13355
  · exact row_13356
  · exact row_13357
  · exact row_13358
  · exact row_13359
  · exact row_13360
  · exact row_13361
  · exact row_13362
  · exact row_13363
  · exact row_13364
  · exact row_13365
  · exact row_13366
  · exact row_13367
  · exact row_13368
  · exact row_13369
  · exact row_13370
  · exact row_13371
  · exact row_13372
  · exact row_13373
  · exact row_13374
  · exact row_13375

end BstLean.Part271.R3.Rows13301
