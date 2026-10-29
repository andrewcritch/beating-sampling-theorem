import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 13226–13300. -/
namespace BstLean.Part271.R3.Rows13226
open Real BstLean.Part130 BstLean.Part227

theorem width_13226 : mW 13226 = 266072392202518 := by
  have hu : mW 13226 ≤ 266072392202518 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13226 ≤ 266072392202517 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13226 : RowArithmetic 13226 (230120283296719659813/200000000000000000000000) (154659806708112971829537/250000000000000000000000) (8483859976695451/1000000000000000000000000) where
  r0 := (65744166297/100000000000000000)
  k0 := (153330081418511/40000000000000000)
  k6 := (11906561974614903/1000000000000000000)
  q := (40660177077823947913/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13226]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13226]

theorem width_13227 : mW 13227 = 266142809667326 := by
  have hu : mW 13227 ≤ 266142809667326 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13227 ≤ 266142809667325 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13227 : RowArithmetic 13227 (17977552693865163349/15625000000000000000000) (19332077461111195608769/31250000000000000000000) (424109317606913/50000000000000000000000) where
  r0 := (328683553801/500000000000000000)
  k0 := (1916517339792723/500000000000000000)
  k6 := (11906111880601677/1000000000000000000)
  q := (32529371343448984643/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13227]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13227]

theorem width_13228 : mW 13228 = 266213240442809 := by
  have hu : mW 13228 ≤ 266213240442809 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13228 ≤ 266213240442808 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13228 : RowArithmetic 13228 (1150525337985781288091/1000000000000000000000000) (309306866312901477760331/500000000000000000000000) (1060064148618569/125000000000000000000000) where
  r0 := (164323141581/250000000000000000)
  k0 := (383281735246299/100000000000000000)
  k6 := (11905661837628199/1000000000000000000)
  q := (81326502445389842303/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13228]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13228]

theorem width_13229 : mW 13229 = 266283684530476 := by
  have hu : mW 13229 ≤ 266283684530476 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13229 ≤ 266283684530475 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13229 : RowArithmetic 13229 (35952728537988274107/31250000000000000000000) (38662561777669443410169/62500000000000000000000) (8478840486963099/1000000000000000000000000) where
  r0 := (657218039133/1000000000000000000)
  k0 := (76652001081831/20000000000000000)
  k6 := (11905211845684823/1000000000000000000)
  q := (162659152831926430147/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13229]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13229]

theorem width_13230 : mW 13230 = 266354141931838 := by
  have hu : mW 13230 ≤ 266354141931838 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13230 ≤ 266354141931837 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13230 : RowArithmetic 13230 (35951540565427956509/31250000000000000000000) (618588246205808097408383/1000000000000000000000000) (8477168246018681/1000000000000000000000000) where
  r0 := (82142940753/125000000000000000)
  k0 := (1916191392230719/500000000000000000)
  k6 := (2380952380952381/200000000000000000)
  q := (81332650270355754589/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13230]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13230]

theorem width_13231 : mW 13231 = 266424612648404 := by
  have hu : mW 13231 ≤ 266424612648404 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13231 ≤ 266424612648403 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13231 : RowArithmetic 13231 (1150411292616787493429/1000000000000000000000000) (154643876478654860135277/250000000000000000000000) (8475496465952213/1000000000000000000000000) where
  r0 := (328534513497/500000000000000000)
  k0 := (3832165543568793/1000000000000000000)
  k6 := (5952156007424903/500000000000000000)
  q := (162671448017161266063/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13231]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13231]

theorem width_13232 : mW 13232 = 266495096681683 := by
  have hu : mW 13232 ≤ 266495096681683 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13232 ≤ 266495096681682 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13232 : RowArithmetic 13232 (575186648390850740609/500000000000000000000000) (618562767568670767082011/1000000000000000000000000) (1694765029320137/200000000000000000000000) where
  r0 := (656994542039/1000000000000000000)
  k0 := (3831948331406839/1000000000000000000)
  k6 := (11903862175938887/1000000000000000000)
  q := (32535519052260408037/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13232]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13232]

theorem width_13233 : mW 13233 = 266565594033185 := by
  have hu : mW 13233 ≤ 266565594033185 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13233 ≤ 266565594033184 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13233 : RowArithmetic 13233 (1150335310585235171857/1000000000000000000000000) (309275015583743943702987/500000000000000000000000) (2118038571950281/250000000000000000000000) where
  r0 := (164230017789/250000000000000000)
  k0 := (3831731147971711/1000000000000000000)
  k6 := (11903412388019513/1000000000000000000)
  q := (81341871136580082977/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13233]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13233]

theorem width_13234 : mW 13234 = 266636104704421 := by
  have hu : mW 13234 ≤ 266636104704421 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13234 ≤ 266636104704420 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13234 : RowArithmetic 13234 (1150297334024187712427/1000000000000000000000000) (77317162088824603638269/125000000000000000000000) (8470483889390599/1000000000000000000000000) where
  r0 := (656845614341/1000000000000000000)
  k0 := (957878498314157/250000000000000000)
  k6 := (2975740662770513/250000000000000000)
  q := (162689889052761972803/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13234]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13234]

theorem width_13235 : mW 13235 = 266706628696899 := by
  have hu : mW 13235 ≤ 266706628696899 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13235 ≤ 266706628696898 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13235 : RowArithmetic 13235 (1150259367095362047281/1000000000000000000000000) (154631141049380933190877/250000000000000000000000) (2117203487801587/250000000000000000000000) where
  r0 := (65677117159/100000000000000000)
  k0 := (478912108406851/125000000000000000)
  k6 := (1487814120639609/125000000000000000)
  q := (16269603560013378519/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13235]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13235]

theorem width_13236 : mW 13236 = 266777166012131 := by
  have hu : mW 13236 ≤ 266777166012131 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13236 ≤ 266777166012130 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13236 : RowArithmetic 13236 (143777676224444903509/125000000000000000000000) (309255916813897417731459/500000000000000000000000) (8467144473085551/1000000000000000000000000) where
  r0 := (6566967429/10000000000000000)
  k0 := (191553988498119/50000000000000000)
  k6 := (5951031665057173/500000000000000000)
  q := (40675545478825480651/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13236]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13236]

theorem width_13237 : mW 13237 = 266847716651625 := by
  have hu : mW 13237 ≤ 266847716651625 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13237 ≤ 266847716651624 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13237 : RowArithmetic 13237 (230036692424316982629/200000000000000000000000) (309249552500468329438523/500000000000000000000000) (8465475454865589/1000000000000000000000000) where
  r0 := (328311164133/500000000000000000)
  k0 := (3830862701369641/1000000000000000000)
  k6 := (11901613746064849/1000000000000000000)
  q := (4067708199957317489/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13237]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13237]

theorem width_13238 : mW 13238 = 266918280616892 := by
  have hu : mW 13238 ≤ 266918280616892 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13238 ≤ 266918280616891 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13238 : RowArithmetic 13238 (575072762035121840391/500000000000000000000000) (154621594579118940243821/250000000000000000000000) (423190344819191/50000000000000000000000) where
  r0 := (131309585537/200000000000000000)
  k0 := (1915322830736359/500000000000000000)
  k6 := (5950582106479379/500000000000000000)
  q := (32542894769826485121/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13238]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13238]

theorem width_13239 : mW 13239 = 266988857909442 := by
  have hu : mW 13239 ≤ 266988857909442 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13239 ≤ 266988857909441 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13239 : RowArithmetic 13239 (575053797819171138729/500000000000000000000000) (618473653573938988712361/1000000000000000000000000) (1692427759495541/200000000000000000000000) where
  r0 := (656473541153/1000000000000000000)
  k0 := (1915214325132409/500000000000000000)
  k6 := (11900714730786453/1000000000000000000)
  q := (40680154866961851329/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13239]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13239]

theorem width_13240 : mW 13240 = 267059448530785 := by
  have hu : mW 13240 ≤ 267059448530785 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13240 ≤ 267059448530784 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13240 : RowArithmetic 13240 (230013935364537760951/200000000000000000000000) (309230465386426584736729/500000000000000000000000) (338418846319391/40000000000000000000000) where
  r0 := (328199584333/500000000000000000)
  k0 := (957552916934787/250000000000000000)
  k6 := (11900265299538317/1000000000000000000)
  q := (32545352970892787661/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13240]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13240]

theorem width_13241 : mW 13241 = 267130052482431 := by
  have hu : mW 13241 ≤ 267130052482431 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13241 ≤ 267130052482430 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13241 : RowArithmetic 13241 (35938492738127897457/31250000000000000000000) (309224104956372729102311/500000000000000000000000) (4229401988871319/500000000000000000000000) where
  r0 := (328162405111/500000000000000000)
  k0 := (3829994713894747/1000000000000000000)
  k6 := (5949907959602367/500000000000000000)
  q := (32546582001801663843/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13241]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13241]

theorem width_13242 : mW 13242 = 267200669765891 := by
  have hu : mW 13242 ≤ 267200669765891 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13242 ≤ 267200669765890 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13242 : RowArithmetic 13242 (229998773605472803761/200000000000000000000000) (77304436374142885866327/125000000000000000000000) (1057142157073617/125000000000000000000000) where
  r0 := (82031308227/125000000000000000)
  k0 := (38297777887219/10000000000000000)
  k6 := (11899366589776091/1000000000000000000)
  q := (162739054931506837727/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13242]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13242]

theorem width_13243 : mW 13243 = 267271300382675 := by
  have hu : mW 13243 ≤ 267271300382675 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13243 ≤ 267271300382674 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13243 : RowArithmetic 13243 (1149955978041314868827/1000000000000000000000000) (618422774013573459218617/1000000000000000000000000) (422773549718071/50000000000000000000000) where
  r0 := (164044033861/250000000000000000)
  k0 := (1914780446106903/500000000000000000)
  k6 := (594945865562139/50000000000000000)
  q := (81372599810992889279/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13243]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13243]

theorem width_13244 : mW 13244 = 267341944334293 := by
  have hu : mW 13244 ≤ 267341944334293 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13244 ≤ 267341944334292 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13244 : RowArithmetic 13244 (229983619531751756873/200000000000000000000000) (154602514743391032651533/250000000000000000000000) (2113451297724477/250000000000000000000000) where
  r0 := (656101819103/1000000000000000000)
  k0 := (3829344024366583/1000000000000000000)
  k6 := (1487308510449399/125000000000000000)
  q := (20343918010058927683/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13244]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13244]

theorem width_13245 : mW 13245 = 267412601622256 := by
  have hu : mW 13245 ≤ 267412601622256 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13245 ≤ 267412601622255 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13245 : RowArithmetic 13245 (574940113438254911863/500000000000000000000000) (123679469174528561498147/200000000000000000000000) (8452139846036263/1000000000000000000000000) where
  r0 := (164006879197/250000000000000000)
  k0 := (1914563592585253/500000000000000000)
  k6 := (11898018906823723/1000000000000000000)
  q := (81378744153495020619/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13245]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13245]

theorem width_13246 : mW 13246 = 267483272248074 := by
  have hu : mW 13246 ≤ 267483272248074 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13246 ≤ 267483272248073 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13246 : RowArithmetic 13246 (28746059142284605143/25000000000000000000000) (154596158677584341028633/250000000000000000000000) (8450474959614447/1000000000000000000000000) where
  r0 := (655953228497/1000000000000000000)
  k0 := (119653449207019/31250000000000000)
  k6 := (1189756978091877/100000000000000000)
  q := (162763632301567907717/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13246]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13246]

theorem width_13247 : mW 13247 = 267553956213257 := by
  have hu : mW 13247 ≤ 267553956213257 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13247 ≤ 267553956213256 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13247 : RowArithmetic 13247 (574902257050099749537/500000000000000000000000) (19324122671442995091853/31250000000000000000000) (264025329108453/31250000000000000000000) where
  r0 := (327939477113/500000000000000000)
  k0 := (3828693592722079/1000000000000000000)
  k6 := (11897120705870733/1000000000000000000)
  q := (10173111004014455361/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13247]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13247]

theorem width_13248 : mW 13248 = 267624653519317 := by
  have hu : mW 13248 ≤ 267624653519317 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13248 ≤ 267624653519316 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13248 : RowArithmetic 13248 (287441668024943251577/250000000000000000000000) (6183592181996864618779/10000000000000000000000) (8447146561442453/1000000000000000000000000) where
  r0 := (65580469397/100000000000000000)
  k0 := (478559604931649/125000000000000000)
  k6 := (92942747513047/7812500000000000)
  q := (81387959797503217669/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13248]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13248]

theorem width_13249 : mW 13249 = 267695364167764 := by
  have hu : mW 13249 ≤ 267695364167764 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13249 ≤ 267695364167763 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13249 : RowArithmetic 13249 (287432209921731248979/250000000000000000000000) (154586628212599373624441/250000000000000000000000) (8445483049368499/1000000000000000000000000) where
  r0 := (655730447727/1000000000000000000)
  k0 := (957065028704243/250000000000000000)
  k6 := (11896222708307023/1000000000000000000)
  q := (162782062893919611367/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13249]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13249]

theorem width_13250 : mW 13250 = 267766088160109 := by
  have hu : mW 13250 ≤ 267766088160109 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13250 ≤ 267766088160108 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13250 : RowArithmetic 13250 (143711377107309534639/125000000000000000000000) (618333809437837508684593/1000000000000000000000000) (168876399901737/20000000000000000000000) where
  r0 := (163914053873/250000000000000000)
  k0 := (765608683760737/200000000000000000)
  k6 := (5947886892886081/500000000000000000)
  q := (81394102980498531937/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13250]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13250]

theorem width_13251 : mW 13251 = 267836825497862 := by
  have hu : mW 13251 ≤ 267836825497862 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13251 ≤ 267836825497861 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13251 : RowArithmetic 13251 (1149653203611249814133/1000000000000000000000000) (618321107961535137913737/1000000000000000000000000) (844215739843583/100000000000000000000000) where
  r0 := (327790998631/500000000000000000)
  k0 := (1913913375704717/500000000000000000)
  k6 := (2973831228513961/250000000000000000)
  q := (81397174398132518959/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13251]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13251]

theorem width_13252 : mW 13252 = 267907576182534 := by
  have hu : mW 13252 ≤ 267907576182534 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13252 ≤ 267907576182533 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13252 : RowArithmetic 13252 (1149615399942069111169/1000000000000000000000000) (123661681684203847934537/200000000000000000000000) (42202476296269/5000000000000000000000) where
  r0 := (655507793033/1000000000000000000)
  k0 := (1913805056313701/500000000000000000)
  k6 := (11894876093148481/1000000000000000000)
  q := (81400245699874886803/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13252]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13252]

theorem width_13253 : mW 13253 = 267978340215637 := by
  have hu : mW 13253 ≤ 267978340215637 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13253 ≤ 267978340215636 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13253 : RowArithmetic 13253 (35924300182742444169/31250000000000000000000) (618295710815818709811103/1000000000000000000000000) (8438833577379161/1000000000000000000000000) where
  r0 := (655433602801/1000000000000000000)
  k0 := (239212093903173/62500000000000000)
  k6 := (11894427323040489/1000000000000000000)
  q := (32561326754295501219/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13253]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13253]

theorem width_13254 : mW 13254 = 268049117598680 := by
  have hu : mW 13254 ≤ 268049117598680 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13254 ≤ 268049117598679 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13254 : RowArithmetic 13254 (1149539821325144930333/1000000000000000000000000) (309141507572731372346339/500000000000000000000000) (8437172352650481/1000000000000000000000000) where
  r0 := (655359426563/1000000000000000000)
  k0 := (956794230218907/250000000000000000)
  k6 := (5946989301861143/500000000000000000)
  q := (20351596988934308199/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13254]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13254]

theorem width_13255 : mW 13255 = 268119908333176 := by
  have hu : mW 13255 ≤ 268119908333176 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13255 ≤ 268119908333175 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13255 : RowArithmetic 13255 (35921938949095474787/31250000000000000000000) (77283790176185077900721/125000000000000000000000) (8435511584906273/1000000000000000000000000) where
  r0 := (131057052863/200000000000000000)
  k0 := (3826960367895159/1000000000000000000)
  k6 := (2973382483796073/250000000000000000)
  q := (162818917819766877359/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13255]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13255]

theorem width_13256 : mW 13256 = 268190712420635 := by
  have hu : mW 13256 ≤ 268190712420635 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13256 ≤ 268190712420634 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13256 : RowArithmetic 13256 (287366070245579673829/250000000000000000000000) (618257629607401779075511/1000000000000000000000000) (131778926156019/15625000000000000000000) where
  r0 := (655211116053/1000000000000000000)
  k0 := (765348768700507/200000000000000000)
  k6 := (1189308131741693/100000000000000000)
  q := (16282505949638096171/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13256]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13256]

theorem width_13257 : mW 13257 = 268261529862568 := by
  have hu : mW 13257 ≤ 268261529862568 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13257 ≤ 268261529862567 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13257 : RowArithmetic 13257 (287356631288941417033/250000000000000000000000) (309122469869377892483511/500000000000000000000000) (2108047854931507/250000000000000000000000) where
  r0 := (327568490887/500000000000000000)
  k0 := (3826527347693847/1000000000000000000)
  k6 := (5946316375205313/500000000000000000)
  q := (81415600470671467007/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13257]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13257]

theorem width_13258 : mW 13258 = 268332360660487 := by
  have hu : mW 13258 ≤ 268332360660487 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13258 ≤ 268332360660486 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13258 : RowArithmetic 13258 (28734719472205672053/25000000000000000000000) (618232251803072476850867/1000000000000000000000000) (8430532021967469/1000000000000000000000000) where
  r0 := (655062861473/1000000000000000000)
  k0 := (3826310880459343/1000000000000000000)
  k6 := (11892184234155807/1000000000000000000)
  q := (162837342154679004697/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13258]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13258]

theorem width_13259 : mW 13259 = 268403204815902 := by
  have hu : mW 13259 ≤ 268403204815902 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13259 ≤ 268403204815901 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13259 : RowArithmetic 13259 (287337760544134014819/250000000000000000000000) (123643913159976341463753/200000000000000000000000) (8428873080548431/1000000000000000000000000) where
  r0 := (163747188787/250000000000000000)
  k0 := (3826094441798033/1000000000000000000)
  k6 := (2378347153728581/200000000000000000)
  q := (162843483136415379243/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13259]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13259]

theorem width_13260 : mW 13260 = 268474062330325 := by
  have hu : mW 13260 ≤ 268474062330325 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13260 ≤ 268474062330324 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13260 : RowArithmetic 13260 (574656657508763327531/500000000000000000000000) (7727586021608919896713/12500000000000000000000) (4213607297653907/500000000000000000000000) where
  r0 := (327457331397/500000000000000000)
  k0 := (1912939015850081/500000000000000000)
  k6 := (743205459616397/62500000000000000)
  q := (32569924777315651639/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13260]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13260]

theorem width_13261 : mW 13261 = 268544933205268 := by
  have hu : mW 13261 ≤ 268544933205268 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13261 ≤ 268544933205267 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13261 : RowArithmetic 13261 (1149275597408033467383/1000000000000000000000000) (309097099794549158125543/500000000000000000000000) (526597285380287/62500000000000000000000) where
  r0 := (654840584409/1000000000000000000)
  k0 := (1912830825082367/500000000000000000)
  k6 := (2378167797960917/200000000000000000)
  q := (32571152881038767431/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13261]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13261]

theorem width_13262 : mW 13262 = 268615817442241 := by
  have hu : mW 13262 ≤ 268615817442241 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13262 ≤ 268615817442240 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13262 : RowArithmetic 13262 (1149237889344894241331/1000000000000000000000000) (618181519380566250196109/1000000000000000000000000) (8423898992717869/1000000000000000000000000) where
  r0 := (654766519987/1000000000000000000)
  k0 := (3825445297179069/1000000000000000000)
  k6 := (297259766911501/25000000000000000)
  q := (40715476173072076697/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13262]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13262]

theorem width_13263 : mW 13263 = 268686715042757 := by
  have hu : mW 13263 ≤ 268686715042757 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13263 ≤ 268686715042756 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13263 : RowArithmetic 13263 (1149200190824945653001/1000000000000000000000000) (618168841102648013880703/1000000000000000000000000) (8422241875046729/1000000000000000000000000) where
  r0 := (327346234763/500000000000000000)
  k0 := (478153621592771/125000000000000000)
  k6 := (11889942413819159/1000000000000000000)
  q := (81434022373943926411/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13263]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13263]

theorem width_13264 : mW 13264 = 268757626008326 := by
  have hu : mW 13264 ≤ 268757626008326 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13264 ≤ 268757626008325 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13264 : RowArithmetic 13264 (143645312730628515779/125000000000000000000000) (309078082377437123839369/500000000000000000000000) (8420585212910421/1000000000000000000000000) where
  r0 := (654618433021/1000000000000000000)
  k0 := (956253169211067/250000000000000000)
  k6 := (2377898840374477/200000000000000000)
  q := (162874184572018656047/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13264]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13264]

theorem width_13265 : mW 13265 = 268828550340461 := by
  have hu : mW 13265 ≤ 268828550340461 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13265 ≤ 268828550340460 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13265 : RowArithmetic 13265 (287281205600495254131/250000000000000000000000) (618143490336775824213847/1000000000000000000000000) (8418929006148169/1000000000000000000000000) where
  r0 := (65454441047/100000000000000000)
  k0 := (3824796409484367/1000000000000000000)
  k6 := (2972261510152541/250000000000000000)
  q := (81440162082353446161/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13265]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13265]

theorem width_13266 : mW 13266 = 268899488040672 := by
  have hu : mW 13266 ≤ 268899488040672 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13266 ≤ 268899488040671 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13266 : RowArithmetic 13266 (1149087152492647423539/1000000000000000000000000) (618130817847883744405773/1000000000000000000000000) (2104318313649841/250000000000000000000000) where
  r0 := (163617600467/250000000000000000)
  k0 := (478072521331587/125000000000000000)
  k6 := (371518685313217/31250000000000000)
  q := (162886463525978732571/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13266]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13266]

theorem width_13267 : mW 13267 = 268970439110472 := by
  have hu : mW 13267 ≤ 268970439110472 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13267 ≤ 268970439110471 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13267 : RowArithmetic 13267 (1149049492113869379251/1000000000000000000000000) (309059073643864590370803/500000000000000000000000) (8415617958103373/1000000000000000000000000) where
  r0 := (163599101803/250000000000000000)
  k0 := (239022747521583/62500000000000000)
  k6 := (475525994804047/40000000000000000)
  q := (81446301327930171393/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13267]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13267]

theorem width_13268 : mW 13268 = 269041403551372 := by
  have hu : mW 13268 ≤ 269041403551372 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13268 ≤ 269041403551371 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13268 : RowArithmetic 13268 (1149011841262491855599/1000000000000000000000000) (618105478655843413324597/1000000000000000000000000) (525872694781231/62500000000000000000000) where
  r0 := (327161213249/500000000000000000)
  k0 := (3824147778555413/1000000000000000000)
  k6 := (742981366302207/62500000000000000)
  q := (40724685388594471007/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13268]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13268]

theorem width_13269 : mW 13269 = 269112381364884 := by
  have hu : mW 13269 ≤ 269112381364884 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13269 ≤ 269112381364883 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13269 : RowArithmetic 13269 (1148974199935360359431/1000000000000000000000000) (309046405975879005552841/500000000000000000000000) (4206154364813937/500000000000000000000000) where
  r0 := (327124229861/500000000000000000)
  k0 := (1911965812638049/500000000000000000)
  k6 := (11887253902215809/1000000000000000000)
  q := (16290488022155751243/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13269]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13269]

theorem width_13270 : mW 13270 = 269183372552521 := by
  have hu : mW 13270 ≤ 269183372552521 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13270 ≤ 269183372552520 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13270 : RowArithmetic 13270 (574468284064660466767/500000000000000000000000) (618080147175004511385099/1000000000000000000000000) (4205327398663743/500000000000000000000000) where
  r0 := (654174506881/1000000000000000000)
  k0 := (3823715500503451/1000000000000000000)
  k6 := (19018889590773/1600000000000000)
  q := (162911018657425379197/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13270]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13270]

theorem width_13271 : mW 13271 = 269254377115793 := by
  have hu : mW 13271 ≤ 269254377115793 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13271 ≤ 269254377115792 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13271 : RowArithmetic 13271 (1148898945841223355921/1000000000000000000000000) (309033742162557389774053/500000000000000000000000) (4204500659719139/500000000000000000000000) where
  r0 := (654100567971/1000000000000000000)
  k0 := (3823499404230613/1000000000000000000)
  k6 := (5943179068438861/500000000000000000)
  q := (81458578431003815303/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13271]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13271]

theorem width_13272 : mW 13272 = 269325395056213 := by
  have hu : mW 13272 ≤ 269325395056213 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13272 ≤ 269325395056212 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13272 : RowArithmetic 13272 (1148861333067916338547/1000000000000000000000000) (618054823401620714352269/1000000000000000000000000) (840734829579997/100000000000000000000000) where
  r0 := (163506660747/250000000000000000)
  k0 := (3823283336450727/1000000000000000000)
  k6 := (11885910330140061/1000000000000000000)
  q := (162923294835330408009/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13272]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13272]

theorem width_13273 : mW 13273 = 269396426375293 := by
  have hu : mW 13273 ≤ 269396426375293 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13273 ≤ 269396426375292 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13273 : RowArithmetic 13273 (1148823729806250727299/1000000000000000000000000) (618042164404054434536821/1000000000000000000000000) (8405695726252387/1000000000000000000000000) where
  r0 := (653952731929/1000000000000000000)
  k0 := (1911533648579927/500000000000000000)
  k6 := (11885462574010609/1000000000000000000)
  q := (40732358144354961959/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13273]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13273]

theorem width_13274 : mW 13274 = 269467471074545 := by
  have hu : mW 13274 ≤ 269467471074545 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13274 ≤ 269467471074544 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13274 : RowArithmetic 13274 (229757227210615740201/200000000000000000000000) (618029507331948178095399/1000000000000000000000000) (8404043610635421/1000000000000000000000000) where
  r0 := (65387883479/100000000000000000)
  k0 := (955712821587783/250000000000000000)
  k6 := (2377002973695967/200000000000000000)
  q := (162935570088302081591/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13274]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13274]

theorem width_13275 : mW 13275 = 269538529155481 := by
  have hu : mW 13275 ≤ 269538529155481 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13275 ≤ 269538529155480 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13275 : RowArithmetic 13275 (574374275902626885349/500000000000000000000000) (77252106523104300456313/125000000000000000000000) (8402391948789039/1000000000000000000000000) where
  r0 := (40862809473/62500000000000000)
  k0 := (1911317652010309/500000000000000000)
  k6 := (11884567213538209/1000000000000000000)
  q := (162941707368003235859/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13275]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13275]

theorem width_13276 : mW 13276 = 269609600619613 := by
  have hu : mW 13276 ≤ 269609600619613 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13276 ≤ 269609600619612 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13276 : RowArithmetic 13276 (229742195411926155779/200000000000000000000000) (77250524870280702787967/125000000000000000000000) (336029629622131/40000000000000000000000) where
  r0 := (326865541129/500000000000000000)
  k0 := (3822419350158523/1000000000000000000)
  k6 := (2376823921835241/200000000000000000)
  q := (10184240276034339519/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13276]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13276]

theorem width_13277 : mW 13277 = 269680685468454 := by
  have hu : mW 13277 ≤ 269680685468454 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13277 ≤ 269680685468453 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13277 : RowArithmetic 13277 (574336705906532550703/500000000000000000000000) (308995773831857295990721/500000000000000000000000) (1679817997153641/200000000000000000000000) where
  r0 := (653657226857/1000000000000000000)
  k0 := (38222034247609/10000000000000000)
  k6 := (11883672055384299/1000000000000000000)
  q := (162953981233966787671/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13277]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13277]

theorem width_13278 : mW 13278 = 269751783703515 := by
  have hu : mW 13278 ≤ 269751783703515 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13278 ≤ 269751783703514 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13278 : RowArithmetic 13278 (1148635856062415039689/1000000000000000000000000) (617978898288774200060909/1000000000000000000000000) (2099359921068509/250000000000000000000000) where
  r0 := (653583385361/1000000000000000000)
  k0 := (3821987527820879/1000000000000000000)
  k6 := (1485403069019121/125000000000000000)
  q := (162960117820281413787/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13278]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13278]

theorem width_13279 : mW 13279 = 269822895326310 := by
  have hu : mW 13279 ≤ 269822895326310 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13279 ≤ 269822895326309 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13279 : RowArithmetic 13279 (1148598309804537832823/1000000000000000000000000) (154491562709239360700733/250000000000000000000000) (8395789835910953/1000000000000000000000000) where
  r0 := (653509557767/1000000000000000000)
  k0 := (382177165933451/100000000000000000)
  k6 := (2376555419894539/200000000000000000)
  q := (40741563543879854391/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13279]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13279]

theorem width_13280 : mW 13280 = 269894020338351 := by
  have hu : mW 13280 ≤ 269894020338351 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13280 ≤ 269894020338350 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13280 : RowArithmetic 13280 (574280386518146822041/500000000000000000000000) (617953605307797565625353/1000000000000000000000000) (8394140440519273/1000000000000000000000000) where
  r0 := (653435744071/1000000000000000000)
  k0 := (1910777909647459/500000000000000000)
  k6 := (11882329697333961/1000000000000000000)
  q := (81486195149853450499/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13280]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13280]

theorem width_13281 : mW 13281 = 269965158741149 := by
  have hu : mW 13281 ≤ 269965158741149 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13281 ≤ 269965158741148 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13281 : RowArithmetic 13281 (143565405719318095081/125000000000000000000000) (1931065505315086984747/3125000000000000000000) (8392491497939417/1000000000000000000000000) where
  r0 := (653361944269/1000000000000000000)
  k0 := (3821340007695227/1000000000000000000)
  k6 := (2376376469145451/200000000000000000)
  q := (40744631548217490293/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13281]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13281]

theorem width_13282 : mW 13282 = 270036310536219 := by
  have hu : mW 13282 ≤ 270036310536219 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13282 ≤ 270036310536218 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13282 : RowArithmetic 13282 (1148485727956151612587/1000000000000000000000000) (617928320015581800649277/1000000000000000000000000) (2097710752002937/250000000000000000000000) where
  r0 := (653288158359/1000000000000000000)
  k0 := (955281056133601/250000000000000000)
  k6 := (5940717522321531/500000000000000000)
  q := (10186541365939668141/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13282]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13282]

theorem width_13283 : mW 13283 = 270107475725071 := by
  have hu : mW 13283 ≤ 270107475725071 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13283 ≤ 270107475725070 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13283 : RowArithmetic 13283 (1148448219637979937363/1000000000000000000000000) (77239460031449140619927/125000000000000000000000) (8389194970576859/1000000000000000000000000) where
  r0 := (130642877267/200000000000000000)
  k0 := (1910454234899861/500000000000000000)
  k6 := (2970246948517969/250000000000000000)
  q := (40747699321556793877/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13283]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13283]

theorem width_13284 : mW 13284 = 270178654309220 := by
  have hu : mW 13284 ≤ 270178654309220 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13284 ≤ 270178654309219 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13284 : RowArithmetic 13284 (1148410720796892820263/1000000000000000000000000) (308951521204197784337251/500000000000000000000000) (1677509477095051/200000000000000000000000) where
  r0 := (326570314097/500000000000000000)
  k0 := (3820692743487221/1000000000000000000)
  k6 := (11880540594004189/1000000000000000000)
  q := (162996932486473499279/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13284]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13284]

theorem width_13285 : mW 13285 = 270249846290177 := by
  have hu : mW 13285 ≤ 270249846290177 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13285 ≤ 270249846290176 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13285 : RowArithmetic 13285 (1148373231429757854363/1000000000000000000000000) (77236300810690394652657/125000000000000000000000) (2096475063136909/250000000000000000000000) where
  r0 := (653066883933/1000000000000000000)
  k0 := (3820477045592939/1000000000000000000)
  k6 := (11880093444430497/1000000000000000000)
  q := (163003067455799739009/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13285]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13285]

theorem width_13286 : mW 13286 = 270321051669455 := by
  have hu : mW 13286 ≤ 270321051669455 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13286 ≤ 270321051669454 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13286 : RowArithmetic 13286 (287083937883360591737/250000000000000000000000) (154469443120627496960039/250000000000000000000000) (8384253571634711/1000000000000000000000000) where
  r0 := (163248288387/250000000000000000)
  k0 := (3820261376109991/1000000000000000000)
  k6 := (5939823172670649/500000000000000000)
  q := (163009202194231967231/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13286]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13286]

theorem width_13287 : mW 13287 = 270392270448568 := by
  have hu : mW 13287 ≤ 270392270448568 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13287 ≤ 270392270448567 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13287 : RowArithmetic 13287 (574149140552407108117/500000000000000000000000) (617865140398890297285287/1000000000000000000000000) (2095651835644307/250000000000000000000000) where
  r0 := (163229859259/250000000000000000)
  k0 := (955011433758603/250000000000000000)
  k6 := (5939599648363547/500000000000000000)
  q := (81507668350898125787/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13287]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13287]

theorem width_13288 : mW 13288 = 270463502629028 := by
  have hu : mW 13288 ≤ 270463502629028 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13288 ≤ 270463502629027 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13288 : RowArithmetic 13288 (287065205035186043311/250000000000000000000000) (308926255117099291912639/500000000000000000000000) (2095240391304017/250000000000000000000000) where
  r0 := (81605716799/125000000000000000)
  k0 := (1909915061178193/500000000000000000)
  k6 := (11878752298578389/1000000000000000000)
  q := (4075536774462966369/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13288]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13288]

theorem width_13289 : mW 13289 = 270534748212348 := by
  have hu : mW 13289 ≤ 270534748212348 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13289 ≤ 270534748212347 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13289 : RowArithmetic 13289 (574111684319051768897/500000000000000000000000) (617839881987969353869511/1000000000000000000000000) (8379316239392149/1000000000000000000000000) where
  r0 := (326386022807/500000000000000000)
  k0 := (381961453807487/100000000000000000)
  k6 := (11878305350885687/1000000000000000000)
  q := (10189225314026577163/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13289]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13289]

theorem width_13290 : mW 13290 = 270606007200041 := by
  have hu : mW 13290 ≤ 270606007200041 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13290 ≤ 270606007200040 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13290 : RowArithmetic 13290 (71761620412110308277/62500000000000000000000) (308913627829868694048541/500000000000000000000000) (8377671364946461/1000000000000000000000000) where
  r0 := (81587296337/125000000000000000)
  k0 := (1909699491088559/500000000000000000)
  k6 := (11877858453639497/1000000000000000000)
  q := (81516869419771022019/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13290]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13290]

theorem width_13291 : mW 13291 = 270677279593620 := by
  have hu : mW 13291 ≤ 270677279593620 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13291 ≤ 270677279593619 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13291 : RowArithmetic 13291 (574074247002301150857/500000000000000000000000) (19306707226532424798301/31250000000000000000000) (16359427620547/1953125000000000000000) where
  r0 := (652624709637/1000000000000000000)
  k0 := (3819183454665009/1000000000000000000)
  k6 := (2969352901707583/250000000000000000)
  q := (32607974484779026213/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13291]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13291]

theorem width_13292 : mW 13292 = 270748565394598 := by
  have hu : mW 13292 ≤ 270748565394598 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13292 ≤ 270748565394597 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13292 : RowArithmetic 13292 (114811107086749091149/100000000000000000000000) (617802008755404998274689/1000000000000000000000000) (8374382969554087/1000000000000000000000000) where
  r0 := (20392220701/31250000000000000)
  k0 := (3818967955528719/1000000000000000000)
  k6 := (11876964810448703/1000000000000000000)
  q := (163046005777510538807/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13292]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13292]

theorem width_13293 : mW 13293 = 270819864604488 := by
  have hu : mW 13293 ≤ 270819864604488 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13293 ≤ 270819864604487 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13293 : RowArithmetic 13293 (574036828589653674087/500000000000000000000000) (308894694089187392813379/500000000000000000000000) (837273944828973/100000000000000000000000) where
  r0 := (652477429077/1000000000000000000)
  k0 := (1909376242380673/500000000000000000)
  k6 := (11876518064485127/1000000000000000000)
  q := (163052138900414305483/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13293]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13293]

theorem width_13294 : mW 13294 = 270891177224804 := by
  have hu : mW 13294 ≤ 270891177224804 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13294 ≤ 270891177224803 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13294 : RowArithmetic 13294 (574018126468464363251/500000000000000000000000) (6177767695174823409243/10000000000000000000000) (1046387047221029/125000000000000000000000) where
  r0 := (652403809569/1000000000000000000)
  k0 := (3818537042358913/1000000000000000000)
  k6 := (5938035684465061/500000000000000000)
  q := (32611654358526492883/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13294]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13294]

theorem width_13295 : mW 13295 = 270962503257059 := by
  have hu : mW 13295 ≤ 270962503257059 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13295 ≤ 270962503257058 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13295 : RowArithmetic 13295 (1147998858137234272907/1000000000000000000000000) (38610259548266448009637/62500000000000000000000) (8369453757830931/1000000000000000000000000) where
  r0 := (2548164859/3906250000000000)
  k0 := (1909160814157257/500000000000000000)
  k6 := (1187562472377421/100000000000000000)
  q := (16306440445419104403/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13295]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13295]

theorem width_13296 : mW 13296 = 271033842702766 := by
  have hu : mW 13296 ≤ 271033842702766 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13296 ≤ 271033842702765 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13296 : RowArithmetic 13296 (1147961472777104532233/1000000000000000000000000) (61775153794225288386269/100000000000000000000000) (4183905794159619/500000000000000000000000) where
  r0 := (652256612079/1000000000000000000)
  k0 := (381810624262417/100000000000000000)
  k6 := (11875178129007913/1000000000000000000)
  q := (163070536885116067861/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13296]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13296]

theorem width_13297 : mW 13297 = 271105195563439 := by
  have hu : mW 13297 ≤ 271105195563439 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13297 ≤ 271105195563438 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13297 : RowArithmetic 13297 (573962048426710288261/500000000000000000000000) (308869462513493694332863/500000000000000000000000) (8366169869074601/1000000000000000000000000) where
  r0 := (65218303409/100000000000000000)
  k0 := (3817890885280969/1000000000000000000)
  k6 := (5937365792310879/500000000000000000)
  q := (163076669085433554547/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13297]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13297]

theorem width_13298 : mW 13298 = 271176561840591 := by
  have hu : mW 13298 ≤ 271176561840591 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13298 ≤ 271176561840590 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13298 : RowArithmetic 13298 (1147886730363065586317/1000000000000000000000000) (123545262805200518901861/200000000000000000000000) (8364528599938569/1000000000000000000000000) where
  r0 := (652109469933/1000000000000000000)
  k0 := (1908837778139001/500000000000000000)
  k6 := (5937142545303137/500000000000000000)
  q := (40770700263792379459/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13298]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13298]

theorem width_13299 : mW 13299 = 271247941535735 := by
  have hu : mW 13299 ≤ 271247941535735 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13299 ≤ 271247941535734 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13299 : RowArithmetic 13299 (573924686651462029207/500000000000000000000000) (308856852469417330047643/500000000000000000000000) (4181443890376381/500000000000000000000000) where
  r0 := (130407183921/200000000000000000)
  k0 := (1908730127805641/500000000000000000)
  k6 := (11873838646951991/1000000000000000000)
  q := (32617786558869993317/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13299]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13299]

theorem width_13300 : mW 13300 = 271319334650386 := by
  have hu : mW 13300 ≤ 271319334650386 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13300 ≤ 271319334650385 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13300 : RowArithmetic 13300 (229562405133976045249/200000000000000000000000) (77212637220627476016789/125000000000000000000000) (1672249482271761/200000000000000000000000) where
  r0 := (651962383101/1000000000000000000)
  k0 := (1908622491635483/500000000000000000)
  k6 := (5936696126824721/500000000000000000)
  q := (81547532151500452381/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13300]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13300]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 13226 then ⟨(230120283296719659813/200000000000000000000000), (154659806708112971829537/250000000000000000000000), (8483859976695451/1000000000000000000000000)⟩ else
  if n = 13227 then ⟨(17977552693865163349/15625000000000000000000), (19332077461111195608769/31250000000000000000000), (424109317606913/50000000000000000000000)⟩ else
  if n = 13228 then ⟨(1150525337985781288091/1000000000000000000000000), (309306866312901477760331/500000000000000000000000), (1060064148618569/125000000000000000000000)⟩ else
  if n = 13229 then ⟨(35952728537988274107/31250000000000000000000), (38662561777669443410169/62500000000000000000000), (8478840486963099/1000000000000000000000000)⟩ else
  if n = 13230 then ⟨(35951540565427956509/31250000000000000000000), (618588246205808097408383/1000000000000000000000000), (8477168246018681/1000000000000000000000000)⟩ else
  if n = 13231 then ⟨(1150411292616787493429/1000000000000000000000000), (154643876478654860135277/250000000000000000000000), (8475496465952213/1000000000000000000000000)⟩ else
  if n = 13232 then ⟨(575186648390850740609/500000000000000000000000), (618562767568670767082011/1000000000000000000000000), (1694765029320137/200000000000000000000000)⟩ else
  if n = 13233 then ⟨(1150335310585235171857/1000000000000000000000000), (309275015583743943702987/500000000000000000000000), (2118038571950281/250000000000000000000000)⟩ else
  if n = 13234 then ⟨(1150297334024187712427/1000000000000000000000000), (77317162088824603638269/125000000000000000000000), (8470483889390599/1000000000000000000000000)⟩ else
  if n = 13235 then ⟨(1150259367095362047281/1000000000000000000000000), (154631141049380933190877/250000000000000000000000), (2117203487801587/250000000000000000000000)⟩ else
  if n = 13236 then ⟨(143777676224444903509/125000000000000000000000), (309255916813897417731459/500000000000000000000000), (8467144473085551/1000000000000000000000000)⟩ else
  if n = 13237 then ⟨(230036692424316982629/200000000000000000000000), (309249552500468329438523/500000000000000000000000), (8465475454865589/1000000000000000000000000)⟩ else
  if n = 13238 then ⟨(575072762035121840391/500000000000000000000000), (154621594579118940243821/250000000000000000000000), (423190344819191/50000000000000000000000)⟩ else
  if n = 13239 then ⟨(575053797819171138729/500000000000000000000000), (618473653573938988712361/1000000000000000000000000), (1692427759495541/200000000000000000000000)⟩ else
  if n = 13240 then ⟨(230013935364537760951/200000000000000000000000), (309230465386426584736729/500000000000000000000000), (338418846319391/40000000000000000000000)⟩ else
  if n = 13241 then ⟨(35938492738127897457/31250000000000000000000), (309224104956372729102311/500000000000000000000000), (4229401988871319/500000000000000000000000)⟩ else
  if n = 13242 then ⟨(229998773605472803761/200000000000000000000000), (77304436374142885866327/125000000000000000000000), (1057142157073617/125000000000000000000000)⟩ else
  if n = 13243 then ⟨(1149955978041314868827/1000000000000000000000000), (618422774013573459218617/1000000000000000000000000), (422773549718071/50000000000000000000000)⟩ else
  if n = 13244 then ⟨(229983619531751756873/200000000000000000000000), (154602514743391032651533/250000000000000000000000), (2113451297724477/250000000000000000000000)⟩ else
  if n = 13245 then ⟨(574940113438254911863/500000000000000000000000), (123679469174528561498147/200000000000000000000000), (8452139846036263/1000000000000000000000000)⟩ else
  if n = 13246 then ⟨(28746059142284605143/25000000000000000000000), (154596158677584341028633/250000000000000000000000), (8450474959614447/1000000000000000000000000)⟩ else
  if n = 13247 then ⟨(574902257050099749537/500000000000000000000000), (19324122671442995091853/31250000000000000000000), (264025329108453/31250000000000000000000)⟩ else
  if n = 13248 then ⟨(287441668024943251577/250000000000000000000000), (6183592181996864618779/10000000000000000000000), (8447146561442453/1000000000000000000000000)⟩ else
  if n = 13249 then ⟨(287432209921731248979/250000000000000000000000), (154586628212599373624441/250000000000000000000000), (8445483049368499/1000000000000000000000000)⟩ else
  if n = 13250 then ⟨(143711377107309534639/125000000000000000000000), (618333809437837508684593/1000000000000000000000000), (168876399901737/20000000000000000000000)⟩ else
  if n = 13251 then ⟨(1149653203611249814133/1000000000000000000000000), (618321107961535137913737/1000000000000000000000000), (844215739843583/100000000000000000000000)⟩ else
  if n = 13252 then ⟨(1149615399942069111169/1000000000000000000000000), (123661681684203847934537/200000000000000000000000), (42202476296269/5000000000000000000000)⟩ else
  if n = 13253 then ⟨(35924300182742444169/31250000000000000000000), (618295710815818709811103/1000000000000000000000000), (8438833577379161/1000000000000000000000000)⟩ else
  if n = 13254 then ⟨(1149539821325144930333/1000000000000000000000000), (309141507572731372346339/500000000000000000000000), (8437172352650481/1000000000000000000000000)⟩ else
  if n = 13255 then ⟨(35921938949095474787/31250000000000000000000), (77283790176185077900721/125000000000000000000000), (8435511584906273/1000000000000000000000000)⟩ else
  if n = 13256 then ⟨(287366070245579673829/250000000000000000000000), (618257629607401779075511/1000000000000000000000000), (131778926156019/15625000000000000000000)⟩ else
  if n = 13257 then ⟨(287356631288941417033/250000000000000000000000), (309122469869377892483511/500000000000000000000000), (2108047854931507/250000000000000000000000)⟩ else
  if n = 13258 then ⟨(28734719472205672053/25000000000000000000000), (618232251803072476850867/1000000000000000000000000), (8430532021967469/1000000000000000000000000)⟩ else
  if n = 13259 then ⟨(287337760544134014819/250000000000000000000000), (123643913159976341463753/200000000000000000000000), (8428873080548431/1000000000000000000000000)⟩ else
  if n = 13260 then ⟨(574656657508763327531/500000000000000000000000), (7727586021608919896713/12500000000000000000000), (4213607297653907/500000000000000000000000)⟩ else
  if n = 13261 then ⟨(1149275597408033467383/1000000000000000000000000), (309097099794549158125543/500000000000000000000000), (526597285380287/62500000000000000000000)⟩ else
  if n = 13262 then ⟨(1149237889344894241331/1000000000000000000000000), (618181519380566250196109/1000000000000000000000000), (8423898992717869/1000000000000000000000000)⟩ else
  if n = 13263 then ⟨(1149200190824945653001/1000000000000000000000000), (618168841102648013880703/1000000000000000000000000), (8422241875046729/1000000000000000000000000)⟩ else
  if n = 13264 then ⟨(143645312730628515779/125000000000000000000000), (309078082377437123839369/500000000000000000000000), (8420585212910421/1000000000000000000000000)⟩ else
  if n = 13265 then ⟨(287281205600495254131/250000000000000000000000), (618143490336775824213847/1000000000000000000000000), (8418929006148169/1000000000000000000000000)⟩ else
  if n = 13266 then ⟨(1149087152492647423539/1000000000000000000000000), (618130817847883744405773/1000000000000000000000000), (2104318313649841/250000000000000000000000)⟩ else
  if n = 13267 then ⟨(1149049492113869379251/1000000000000000000000000), (309059073643864590370803/500000000000000000000000), (8415617958103373/1000000000000000000000000)⟩ else
  if n = 13268 then ⟨(1149011841262491855599/1000000000000000000000000), (618105478655843413324597/1000000000000000000000000), (525872694781231/62500000000000000000000)⟩ else
  if n = 13269 then ⟨(1148974199935360359431/1000000000000000000000000), (309046405975879005552841/500000000000000000000000), (4206154364813937/500000000000000000000000)⟩ else
  if n = 13270 then ⟨(574468284064660466767/500000000000000000000000), (618080147175004511385099/1000000000000000000000000), (4205327398663743/500000000000000000000000)⟩ else
  if n = 13271 then ⟨(1148898945841223355921/1000000000000000000000000), (309033742162557389774053/500000000000000000000000), (4204500659719139/500000000000000000000000)⟩ else
  if n = 13272 then ⟨(1148861333067916338547/1000000000000000000000000), (618054823401620714352269/1000000000000000000000000), (840734829579997/100000000000000000000000)⟩ else
  if n = 13273 then ⟨(1148823729806250727299/1000000000000000000000000), (618042164404054434536821/1000000000000000000000000), (8405695726252387/1000000000000000000000000)⟩ else
  if n = 13274 then ⟨(229757227210615740201/200000000000000000000000), (618029507331948178095399/1000000000000000000000000), (8404043610635421/1000000000000000000000000)⟩ else
  if n = 13275 then ⟨(574374275902626885349/500000000000000000000000), (77252106523104300456313/125000000000000000000000), (8402391948789039/1000000000000000000000000)⟩ else
  if n = 13276 then ⟨(229742195411926155779/200000000000000000000000), (77250524870280702787967/125000000000000000000000), (336029629622131/40000000000000000000000)⟩ else
  if n = 13277 then ⟨(574336705906532550703/500000000000000000000000), (308995773831857295990721/500000000000000000000000), (1679817997153641/200000000000000000000000)⟩ else
  if n = 13278 then ⟨(1148635856062415039689/1000000000000000000000000), (617978898288774200060909/1000000000000000000000000), (2099359921068509/250000000000000000000000)⟩ else
  if n = 13279 then ⟨(1148598309804537832823/1000000000000000000000000), (154491562709239360700733/250000000000000000000000), (8395789835910953/1000000000000000000000000)⟩ else
  if n = 13280 then ⟨(574280386518146822041/500000000000000000000000), (617953605307797565625353/1000000000000000000000000), (8394140440519273/1000000000000000000000000)⟩ else
  if n = 13281 then ⟨(143565405719318095081/125000000000000000000000), (1931065505315086984747/3125000000000000000000), (8392491497939417/1000000000000000000000000)⟩ else
  if n = 13282 then ⟨(1148485727956151612587/1000000000000000000000000), (617928320015581800649277/1000000000000000000000000), (2097710752002937/250000000000000000000000)⟩ else
  if n = 13283 then ⟨(1148448219637979937363/1000000000000000000000000), (77239460031449140619927/125000000000000000000000), (8389194970576859/1000000000000000000000000)⟩ else
  if n = 13284 then ⟨(1148410720796892820263/1000000000000000000000000), (308951521204197784337251/500000000000000000000000), (1677509477095051/200000000000000000000000)⟩ else
  if n = 13285 then ⟨(1148373231429757854363/1000000000000000000000000), (77236300810690394652657/125000000000000000000000), (2096475063136909/250000000000000000000000)⟩ else
  if n = 13286 then ⟨(287083937883360591737/250000000000000000000000), (154469443120627496960039/250000000000000000000000), (8384253571634711/1000000000000000000000000)⟩ else
  if n = 13287 then ⟨(574149140552407108117/500000000000000000000000), (617865140398890297285287/1000000000000000000000000), (2095651835644307/250000000000000000000000)⟩ else
  if n = 13288 then ⟨(287065205035186043311/250000000000000000000000), (308926255117099291912639/500000000000000000000000), (2095240391304017/250000000000000000000000)⟩ else
  if n = 13289 then ⟨(574111684319051768897/500000000000000000000000), (617839881987969353869511/1000000000000000000000000), (8379316239392149/1000000000000000000000000)⟩ else
  if n = 13290 then ⟨(71761620412110308277/62500000000000000000000), (308913627829868694048541/500000000000000000000000), (8377671364946461/1000000000000000000000000)⟩ else
  if n = 13291 then ⟨(574074247002301150857/500000000000000000000000), (19306707226532424798301/31250000000000000000000), (16359427620547/1953125000000000000000)⟩ else
  if n = 13292 then ⟨(114811107086749091149/100000000000000000000000), (617802008755404998274689/1000000000000000000000000), (8374382969554087/1000000000000000000000000)⟩ else
  if n = 13293 then ⟨(574036828589653674087/500000000000000000000000), (308894694089187392813379/500000000000000000000000), (837273944828973/100000000000000000000000)⟩ else
  if n = 13294 then ⟨(574018126468464363251/500000000000000000000000), (6177767695174823409243/10000000000000000000000), (1046387047221029/125000000000000000000000)⟩ else
  if n = 13295 then ⟨(1147998858137234272907/1000000000000000000000000), (38610259548266448009637/62500000000000000000000), (8369453757830931/1000000000000000000000000)⟩ else
  if n = 13296 then ⟨(1147961472777104532233/1000000000000000000000000), (61775153794225288386269/100000000000000000000000), (4183905794159619/500000000000000000000000)⟩ else
  if n = 13297 then ⟨(573962048426710288261/500000000000000000000000), (308869462513493694332863/500000000000000000000000), (8366169869074601/1000000000000000000000000)⟩ else
  if n = 13298 then ⟨(1147886730363065586317/1000000000000000000000000), (123545262805200518901861/200000000000000000000000), (8364528599938569/1000000000000000000000000)⟩ else
  if n = 13299 then ⟨(573924686651462029207/500000000000000000000000), (308856852469417330047643/500000000000000000000000), (4181443890376381/500000000000000000000000)⟩ else
  ⟨(229562405133976045249/200000000000000000000000), (77212637220627476016789/125000000000000000000000), (1672249482271761/200000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 13226 ≤ n) (hb : n ≤ 13300) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_13226
  · exact row_13227
  · exact row_13228
  · exact row_13229
  · exact row_13230
  · exact row_13231
  · exact row_13232
  · exact row_13233
  · exact row_13234
  · exact row_13235
  · exact row_13236
  · exact row_13237
  · exact row_13238
  · exact row_13239
  · exact row_13240
  · exact row_13241
  · exact row_13242
  · exact row_13243
  · exact row_13244
  · exact row_13245
  · exact row_13246
  · exact row_13247
  · exact row_13248
  · exact row_13249
  · exact row_13250
  · exact row_13251
  · exact row_13252
  · exact row_13253
  · exact row_13254
  · exact row_13255
  · exact row_13256
  · exact row_13257
  · exact row_13258
  · exact row_13259
  · exact row_13260
  · exact row_13261
  · exact row_13262
  · exact row_13263
  · exact row_13264
  · exact row_13265
  · exact row_13266
  · exact row_13267
  · exact row_13268
  · exact row_13269
  · exact row_13270
  · exact row_13271
  · exact row_13272
  · exact row_13273
  · exact row_13274
  · exact row_13275
  · exact row_13276
  · exact row_13277
  · exact row_13278
  · exact row_13279
  · exact row_13280
  · exact row_13281
  · exact row_13282
  · exact row_13283
  · exact row_13284
  · exact row_13285
  · exact row_13286
  · exact row_13287
  · exact row_13288
  · exact row_13289
  · exact row_13290
  · exact row_13291
  · exact row_13292
  · exact row_13293
  · exact row_13294
  · exact row_13295
  · exact row_13296
  · exact row_13297
  · exact row_13298
  · exact row_13299
  · exact row_13300

end BstLean.Part271.R3.Rows13226
