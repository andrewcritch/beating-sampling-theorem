import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15280–15354. -/
namespace BstLean.Part271.R3.Rows15280
open Real BstLean.Part130 BstLean.Part227

theorem width_15280 : mW 15280 = 440993044667411 := by
  have hu : mW 15280 ≤ 440993044667411 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15280 ≤ 440993044667410 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15280 : RowArithmetic 15280 (108900041932504406257/100000000000000000000000) (297987636831313137788647/500000000000000000000000) (5826629780221237/1000000000000000000000000) where
  r0 := (529437828609/1000000000000000000)
  k0 := (214993963118473/62500000000000000)
  k6 := (2215485717252717/200000000000000000)
  q := (2731471672926519661/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15280]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15280]

theorem width_15281 : mW 15281 = 441094065735897 := by
  have hu : mW 15281 ≤ 441094065735897 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15281 ≤ 441094065735896 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15281 : RowArithmetic 15281 (544488478809346648137/500000000000000000000000) (595965711627800721896601/1000000000000000000000000) (5825639909473269/1000000000000000000000000) where
  r0 := (529385859251/1000000000000000000)
  k0 := (1719867288067589/500000000000000000)
  k6 := (11077066122752657/1000000000000000000)
  q := (174819907333232504491/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15281]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15281]

theorem width_15282 : mW 15282 = 441195103332970 := by
  have hu : mW 15282 ≤ 441195103332970 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15282 ≤ 441195103332969 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15282 : RowArithmetic 15282 (21779070020802844253/20000000000000000000000) (297978075411404883706717/500000000000000000000000) (5824650273816819/1000000000000000000000000) where
  r0 := (105866779679/200000000000000000)
  k0 := (1719782880855041/500000000000000000)
  k6 := (2215340738963961/200000000000000000)
  q := (87412813706000792479/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15282]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15282]

theorem width_15283 : mW 15283 = 441296157460252 := by
  have hu : mW 15283 ≤ 441296157460252 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15283 ≤ 441296157460251 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15283 : RowArithmetic 15283 (1088930049587923563619/1000000000000000000000000) (595946591247400526431343/1000000000000000000000000) (1455915218295051/250000000000000000000000) where
  r0 := (529281946039/1000000000000000000)
  k0 := (3439396966616627/1000000000000000000)
  k6 := (11076341302459209/1000000000000000000)
  q := (2185391841295285883/12500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15283]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15283]

theorem width_15284 : mW 15284 = 441397228119366 := by
  have hu : mW 15284 ≤ 441397228119366 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15284 ≤ 441397228119365 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15284 : RowArithmetic 15284 (544453301630285143527/500000000000000000000000) (37246064556332517000547/62500000000000000000000) (1455667926872939/250000000000000000000000) where
  r0 := (529230002181/1000000000000000000)
  k0 := (1719614095425581/500000000000000000)
  k6 := (11075978945665051/1000000000000000000)
  q := (17483706700811472947/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15284]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15284]

theorem width_15285 : mW 15285 = 441498315311934 := by
  have hu : mW 15285 ≤ 441498315311934 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15285 ≤ 441498315311933 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15285 : RowArithmetic 15285 (217776632411323241859/200000000000000000000000) (595927475784316294520507/1000000000000000000000000) (5821682776679847/1000000000000000000000000) where
  r0 := (264589033409/500000000000000000)
  k0 := (3439059434406783/1000000000000000000)
  k6 := (5537808312215757/500000000000000000)
  q := (1398742292203964211/8000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15285]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15285]

theorem width_15286 : mW 15286 = 441599419039579 := by
  have hu : mW 15286 ≤ 441599419039579 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15286 ≤ 441599419039578 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15286 : RowArithmetic 15286 (136107465746824417799/125000000000000000000000) (595917919896135986927003/1000000000000000000000000) (5820694080672863/1000000000000000000000000) where
  r0 := (529126139949/1000000000000000000)
  k0 := (3438890697283087/1000000000000000000)
  k6 := (11075254338752781/1000000000000000000)
  q := (2185606323197295291/12500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15286]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15286]

theorem width_15287 : mW 15287 = 441700539303923 := by
  have hu : mW 15287 ≤ 441700539303923 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15287 ≤ 441700539303922 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15287 : RowArithmetic 15287 (1088836295013042586087/1000000000000000000000000) (595908365236526757993287/1000000000000000000000000) (581970561939923/100000000000000000000000) where
  r0 := (132268555393/250000000000000000)
  k0 := (53730030929319/15625000000000000)
  k6 := (11074892088623037/1000000000000000000)
  q := (174854224998997379103/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15287]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15287]

theorem width_15288 : mW 15288 = 441801676106590 := by
  have hu : mW 15288 ≤ 441801676106590 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15288 ≤ 441801676106589 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15288 : RowArithmetic 15288 (544406434585246337471/500000000000000000000000) (595898811805236194338229/1000000000000000000000000) (5818717392787377/1000000000000000000000000) where
  r0 := (105804462337/200000000000000000)
  k0 := (859638320245779/250000000000000000)
  k6 := (1107452987403647/100000000000000000)
  q := (43714985988788787441/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15288]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15288]

theorem width_15289 : mW 15289 = 441902829449201 := by
  have hu : mW 15289 ≤ 441902829449201 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15289 ≤ 441902829449200 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15289 : RowArithmetic 15289 (544394724222740966001/500000000000000000000000) (297944629801005912293869/500000000000000000000000) (2908864700382899/500000000000000000000000) where
  r0 := (264485205143/500000000000000000)
  k0 := (3438384601799529/1000000000000000000)
  k6 := (11074167694987267/1000000000000000000)
  q := (8743283136213764409/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15289]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15289]

theorem width_15290 : mW 15290 = 442003999333381 := by
  have hu : mW 15290 ≤ 442003999333381 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15290 ≤ 442003999333380 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15290 : RowArithmetic 15290 (1088766032836545813859/1000000000000000000000000) (119175941725320262191817/200000000000000000000000) (2908370821631481/500000000000000000000000) where
  r0 := (528918517373/1000000000000000000)
  k0 := (687643188384399/200000000000000000)
  k6 := (5536902775734809/500000000000000000)
  q := (34974276261275228853/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15290]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15290]

theorem width_15291 : mW 15291 = 442105185760752 := by
  have hu : mW 15291 ≤ 442105185760752 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15291 ≤ 442105185760751 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15291 : RowArithmetic 15291 (1088742622342221364813/1000000000000000000000000) (148967539719688103485397/250000000000000000000000) (2907877060103703/500000000000000000000000) where
  r0 := (33054164559/62500000000000000)
  k0 := (3438047301346857/1000000000000000000)
  k6 := (11073443443477713/1000000000000000000)
  q := (174877099701476064937/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15291]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15291]

theorem width_15292 : mW 15292 = 442206388732936 := by
  have hu : mW 15292 ≤ 442206388732936 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15292 ≤ 442206388732935 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15292 : RowArithmetic 15292 (108871921696104616427/100000000000000000000000) (595860610358212943620069/1000000000000000000000000) (1453691707881923/250000000000000000000000) where
  r0 := (528814756997/1000000000000000000)
  k0 := (859469670017613/250000000000000000)
  k6 := (2214616274201149/200000000000000000)
  q := (174882817909593394109/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15292]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15292]

theorem width_15293 : mW 15293 = 442307608251558 := by
  have hu : mW 15293 ≤ 442307608251558 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15293 ≤ 442307608251557 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15293 : RowArithmetic 15293 (544347908345778638269/500000000000000000000000) (148962765766182678850173/250000000000000000000000) (1453444944288093/250000000000000000000000) where
  r0 := (52876288953/100000000000000000)
  k0 := (21485687988057/6250000000000000)
  k6 := (11072719334047907/1000000000000000000)
  q := (1748885359307464727/10000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15293]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15293]

theorem width_15294 : mW 15294 = 442408844318239 := by
  have hu : mW 15294 ≤ 442408844318239 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15294 ≤ 442408844318238 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15294 : RowArithmetic 15294 (544336210766146850763/500000000000000000000000) (595841516998053790312277/1000000000000000000000000) (1453198239252519/250000000000000000000000) where
  r0 := (264355515271/500000000000000000)
  k0 := (3437541495402449/1000000000000000000)
  k6 := (11072357332598393/1000000000000000000)
  q := (43723563441238409657/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15294]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15294]

theorem width_15295 : mW 15295 = 442510096934603 := by
  have hu : mW 15295 ≤ 442510096934603 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15295 ≤ 442510096934602 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15295 : RowArithmetic 15295 (544324515740896961901/500000000000000000000000) (297915986078965042183301/500000000000000000000000) (5811806371029423/1000000000000000000000000) where
  r0 := (528659180029/1000000000000000000)
  k0 := (3437372932000273/1000000000000000000)
  k6 := (55359976833257/5000000000000000)
  q := (34979994282446645363/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15295]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15295]

theorem width_15296 : mW 15296 = 442611366102274 := by
  have hu : mW 15296 ≤ 442611366102274 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15296 ≤ 442611366102273 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15296 : RowArithmetic 15296 (217725129307719392619/200000000000000000000000) (595822428544107741522947/1000000000000000000000000) (290541000956953/50000000000000000000000) where
  r0 := (66075917249/125000000000000000)
  k0 := (3437204387888681/1000000000000000000)
  k6 := (2767908359050281/250000000000000000)
  q := (5465802777268861537/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15296]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15296]

theorem width_15297 : mW 15297 = 442712651822874 := by
  have hu : mW 15297 ≤ 442712651822874 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15297 ≤ 442712651822873 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15297 : RowArithmetic 15297 (1088602266701243072939/1000000000000000000000000) (595812886156334882960951/1000000000000000000000000) (2904916950633843/500000000000000000000000) where
  r0 := (264277752213/500000000000000000)
  k0 := (1718517931527127/500000000000000000)
  k6 := (2214254308248353/200000000000000000)
  q := (21863925768260374333/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15297]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15297]

theorem width_15298 : mW 15298 = 442813954098027 := by
  have hu : mW 15298 ≤ 442813954098027 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15298 ≤ 442813954098026 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15298 : RowArithmetic 15298 (17009045187004255341/15625000000000000000000) (5958033449943597516877/10000000000000000000000) (5808848017344001/1000000000000000000000000) where
  r0 := (132125919833/250000000000000000)
  k0 := (85921683937577/25000000000000000)
  k6 := (5535454840883761/500000000000000000)
  q := (174917123232689829189/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15298]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15298]

theorem width_15299 : mW 15299 = 442915272929357 := by
  have hu : mW 15299 ≤ 442915272929357 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15299 ≤ 442915272929356 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15299 : RowArithmetic 15299 (217711104467645078527/200000000000000000000000) (29789690252896533042039/50000000000000000000000) (2903931183648367/500000000000000000000000) where
  r0 := (105690372541/200000000000000000)
  k0 := (429587358902717/125000000000000000)
  k6 := (2767636964443149/250000000000000000)
  q := (34984568026488479139/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15299]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15299]

theorem width_15300 : mW 15300 = 443016608318485 := by
  have hu : mW 15300 ≤ 443016608318485 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15300 ≤ 443016608318484 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15300 : RowArithmetic 15300 (544266078904822214783/500000000000000000000000) (119156853269359198739907/200000000000000000000000) (5806876951054677/1000000000000000000000000) where
  r0 := (264200027273/500000000000000000)
  k0 := (859132601054077/250000000000000000)
  k6 := (1383773258656399/125000000000000000)
  q := (174928556845359014127/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15300]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15300]

theorem width_15301 : mW 15301 = 443117960267037 := by
  have hu : mW 15301 ≤ 443117960267037 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15301 ≤ 443117960267036 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15301 : RowArithmetic 15301 (1088508798381070444507/1000000000000000000000000) (29788736443035209299339/50000000000000000000000) (1451472942136647/250000000000000000000000) where
  r0 := (528348254851/1000000000000000000)
  k0 := (214772622279789/62500000000000000)
  k6 := (11069824316197511/1000000000000000000)
  q := (34986854674291600287/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15301]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15301]

theorem width_15302 : mW 15302 = 443219328776635 := by
  have hu : mW 15302 ≤ 443219328776635 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15302 ≤ 443219328776634 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15302 : RowArithmetic 15302 (1088485444051046359207/1000000000000000000000000) (297882596299701850403731/500000000000000000000000) (2902453409850651/500000000000000000000000) where
  r0 := (528296463619/1000000000000000000)
  k0 := (687238705600453/200000000000000000)
  k6 := (34592070620643/3125000000000000)
  q := (87469994855378835789/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15302]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15302]

theorem width_15303 : mW 15303 = 443320713848903 := by
  have hu : mW 15303 ≤ 443320713848903 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15303 ≤ 443320713848902 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15303 : RowArithmetic 15303 (272115523704528732607/250000000000000000000000) (297877828781321600539957/500000000000000000000000) (2901961052223827/500000000000000000000000) where
  r0 := (33015292553/62500000000000000)
  k0 := (3436025118789559/1000000000000000000)
  k6 := (2213820183294029/200000000000000000)
  q := (174945705863276335521/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15303]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15303]

theorem width_15304 : mW 15304 = 443422115485465 := by
  have hu : mW 15304 ≤ 443422115485465 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15304 ≤ 443422115485464 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15304 : RowArithmetic 15304 (1088438750680819448071/1000000000000000000000000) (37234132734385707292229/62500000000000000000000) (580293762271451/100000000000000000000000) where
  r0 := (105638581307/200000000000000000)
  k0 := (3435856728831581/1000000000000000000)
  k6 := (5534369634892437/500000000000000000)
  q := (87475710914516150619/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15304]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15304]

theorem width_15305 : mW 15305 = 443523533687944 := by
  have hu : mW 15305 ≤ 443523533687944 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15305 ≤ 443523533687943 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15305 : RowArithmetic 15305 (217683082327540816663/200000000000000000000000) (119147318232347350399053/200000000000000000000000) (5801953374430771/1000000000000000000000000) where
  r0 := (13203528517/25000000000000000)
  k0 := (3435688358131163/1000000000000000000)
  k6 := (11068377658544157/1000000000000000000)
  q := (174957137608043873713/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15305]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15305]

theorem width_15306 : mW 15306 = 443624968457964 := by
  have hu : mW 15306 ≤ 443624968457964 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15306 ≤ 443624968457963 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15306 : RowArithmetic 15306 (1088392077687313191181/1000000000000000000000000) (595727059797088319808357/1000000000000000000000000) (5800969359525357/1000000000000000000000000) where
  r0 := (528089383279/1000000000000000000)
  k0 := (3435520006678123/1000000000000000000)
  k6 := (2767004020685551/250000000000000000)
  q := (8748142660016467747/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15306]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15306]

theorem width_15307 : mW 15307 = 443726419797149 := by
  have hu : mW 15307 ≤ 443726419797149 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15307 ≤ 443726419797148 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15307 : RowArithmetic 15307 (1088368748828191659073/1000000000000000000000000) (119143505931194981180631/200000000000000000000000) (5799985577927213/1000000000000000000000000) where
  r0 := (132009408583/250000000000000000)
  k0 := (1717675837237647/500000000000000000)
  k6 := (5533827271186613/500000000000000000)
  q := (43742142151476760981/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15307]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15307]

theorem width_15308 : mW 15308 = 443827887707122 := by
  have hu : mW 15308 ≤ 443827887707122 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15308 ≤ 443827887707121 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15308 : RowArithmetic 15308 (27208635626472131363/25000000000000000000000) (7446350009226817829521/12500000000000000000000) (2899501014782661/500000000000000000000000) where
  r0 := (131996473459/250000000000000000)
  k0 := (107349480047367/31250000000000000)
  k6 := (5533646518715719/500000000000000000)
  q := (4374357095619880917/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15308]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15308]

theorem width_15309 : mW 15309 = 443929372189508 := by
  have hu : mW 15309 ≤ 443929372189508 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15309 ≤ 443929372189507 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15309 : RowArithmetic 15309 (544161053188969790337/500000000000000000000000) (595698473043348913030011/1000000000000000000000000) (181188084824021/31250000000000000000000) where
  r0 := (527934161789/1000000000000000000)
  k0 := (687003013559159/200000000000000000)
  k6 := (11066931567911053/1000000000000000000)
  q := (174979998857012226237/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15309]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15309]

theorem width_15310 : mW 15310 = 444030873245930 := by
  have hu : mW 15310 ≤ 444030873245930 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15310 ≤ 444030873245929 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15310 : RowArithmetic 15310 (217659758556780293661/200000000000000000000000) (29784447328566721251147/50000000000000000000000) (2898517816133151/500000000000000000000000) where
  r0 := (527882438189/1000000000000000000)
  k0 := (3434846793311771/1000000000000000000)
  k6 := (11066570133806287/1000000000000000000)
  q := (87492856851288151317/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15310]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15310]

theorem width_15311 : mW 15311 = 444132390878013 := by
  have hu : mW 15311 ≤ 444132390878013 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15311 ≤ 444132390878012 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15311 : RowArithmetic 15311 (544137742137658791917/500000000000000000000000) (595679421321851116593089/1000000000000000000000000) (5796052783187251/1000000000000000000000000) where
  r0 := (105566144607/200000000000000000)
  k0 := (3434678538063243/1000000000000000000)
  k6 := (11066208735111359/1000000000000000000)
  q := (87495714180752876463/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15311]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15311]

theorem width_15312 : mW 15312 = 444233925087380 := by
  have hu : mW 15312 ≤ 444233925087380 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15312 ≤ 444233925087379 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15312 : RowArithmetic 15312 (1088252180850735820267/1000000000000000000000000) (297834948647324104509493/500000000000000000000000) (2897535083530307/500000000000000000000000) where
  r0 := (131944754081/250000000000000000)
  k0 := (3434510302043277/1000000000000000000)
  k6 := (2213169474364097/200000000000000000)
  q := (87498571416909430591/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15312]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15312]

theorem width_15313 : mW 15313 = 444335475875655 := by
  have hu : mW 15313 ≤ 444335475875655 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15313 ≤ 444335475875654 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15313 : RowArithmetic 15313 (1088228882508704253621/1000000000000000000000000) (297830187244737522619247/500000000000000000000000) (5794087783815497/1000000000000000000000000) where
  r0 := (263863659027/500000000000000000)
  k0 := (3434342085248193/1000000000000000000)
  k6 := (11065486043927887/1000000000000000000)
  q := (175002857119533908483/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15313]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15313]

theorem width_15314 : mW 15314 = 444437043244464 := by
  have hu : mW 15314 ≤ 444437043244464 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15314 ≤ 444437043244463 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15314 : RowArithmetic 15314 (217641117849554159227/200000000000000000000000) (119130170581216189353989/200000000000000000000000) (5793105633381009/1000000000000000000000000) where
  r0 := (8244931691/15625000000000000)
  k0 := (85854347191939/25000000000000000)
  k6 := (2213024950285557/200000000000000000)
  q := (17500857121866917293/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15314]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15314]

theorem width_15315 : mW 15315 = 444538627195428 := by
  have hu : mW 15315 ≤ 444538627195428 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15315 ≤ 444538627195427 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15315 : RowArithmetic 15315 (1088182301066485626821/1000000000000000000000000) (297820666272107657015981/500000000000000000000000) (5792123715686351/1000000000000000000000000) where
  r0 := (32976496677/62500000000000000)
  k0 := (686801141865539/200000000000000000)
  k6 := (5532381747157201/500000000000000000)
  q := (43753571282810732409/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15315]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15315]

theorem width_15316 : mW 15316 = 444640227730174 := by
  have hu : mW 15316 ≤ 444640227730174 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15316 ≤ 444640227730173 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15316 : RowArithmetic 15316 (136019877245424671451/125000000000000000000000) (9306747084431683110261/15625000000000000000000) (5791142030660671/1000000000000000000000000) where
  r0 := (131893068469/250000000000000000)
  k0 := (3433837550194913/1000000000000000000)
  k6 := (11064402272581961/1000000000000000000)
  q := (43754999714318362683/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15316]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15316]

theorem width_15317 : mW 15317 = 444741844850326 := by
  have hu : mW 15317 ≤ 444741844850326 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15317 ≤ 444741844850325 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15317 : RowArithmetic 15317 (1088135739937056228293/1000000000000000000000000) (119124459096813536316937/200000000000000000000000) (1158032115646637/200000000000000000000000) where
  r0 := (527520609353/1000000000000000000)
  k0 := (137346776410891/40000000000000000)
  k6 := (11064041086224687/1000000000000000000)
  q := (175025712396779005369/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15317]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15317]

theorem width_15318 : mW 15318 = 444843478557506 := by
  have hu : mW 15318 ≤ 444843478557506 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15318 ≤ 444843478557505 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15318 : RowArithmetic 15318 (1088112466986013617643/1000000000000000000000000) (297806389392642439133043/500000000000000000000000) (2894589679166581/500000000000000000000000) where
  r0 := (263734476631/500000000000000000)
  k0 := (858375322389837/250000000000000000)
  k6 := (1382959991904601/125000000000000000)
  q := (175031425749777859713/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15318]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15318]

theorem width_15319 : mW 15319 = 444945128853341 := by
  have hu : mW 15319 ≤ 444945128853341 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15319 ≤ 444945128853340 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15319 : RowArithmetic 15319 (108808919910881975603/100000000000000000000000) (297801631653514516794193/500000000000000000000000) (723524796361229/125000000000000000000000) where
  r0 := (527417305601/1000000000000000000)
  k0 := (3433333188052443/1000000000000000000)
  k6 := (11063318819612551/1000000000000000000)
  q := (3500742778325765539/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15319]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15319]

theorem width_15320 : mW 15320 = 445046795739455 := by
  have hu : mW 15320 ≤ 445046795739455 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15320 ≤ 445046795739454 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15320 : RowArithmetic 15320 (1088065936304026429761/1000000000000000000000000) (37224609315565617599531/62500000000000000000000) (5787217615832491/1000000000000000000000000) where
  r0 := (8240088537/15625000000000000)
  k0 := (3433165105747873/1000000000000000000)
  k6 := (2212591547869229/200000000000000000)
  q := (87521425948164258643/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15320]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15320]

theorem width_15321 : mW 15321 = 445148479217471 := by
  have hu : mW 15321 ≤ 445148479217471 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15321 ≤ 445148479217470 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15321 : RowArithmetic 15321 (1088042678570186300291/1000000000000000000000000) (297792118005548689766989/500000000000000000000000) (231449483723619/40000000000000000000000) where
  r0 := (527314035561/1000000000000000000)
  k0 := (3432997042641947/1000000000000000000)
  k6 := (11062596694431819/1000000000000000000)
  q := (175048564689916837947/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15321]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15321]

theorem width_15322 : mW 15322 = 445250179289016 := by
  have hu : mW 15322 ≤ 445250179289016 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15322 ≤ 445250179289015 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15322 : RowArithmetic 15322 (544009712952925586291/500000000000000000000000) (595574724192921337931617/1000000000000000000000000) (723157100324137/125000000000000000000000) where
  r0 := (527262413179/1000000000000000000)
  k0 := (343282899873423/100000000000000000)
  k6 := (11062235684863807/1000000000000000000)
  q := (8752713864853574659/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15322]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15322]

theorem width_15323 : mW 15323 = 445351895955712 := by
  have hu : mW 15323 ≤ 445351895955712 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15323 ≤ 445351895955711 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15323 : RowArithmetic 15323 (135999522288696888953/125000000000000000000000) (595565213594271877476617/1000000000000000000000000) (1446069186067439/250000000000000000000000) where
  r0 := (263605399609/500000000000000000)
  k0 := (3432660974014519/1000000000000000000)
  k6 := (11061874710636341/1000000000000000000)
  q := (175059989717810734253/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15323]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15323]

theorem width_15324 : mW 15324 = 445453629219185 := by
  have hu : mW 15324 ≤ 445453629219185 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15324 ≤ 445453629219184 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15324 : RowArithmetic 15324 (1087972935779911325941/1000000000000000000000000) (595555704214898952951263/1000000000000000000000000) (2891648459024917/500000000000000000000000) where
  r0 := (263579596839/500000000000000000)
  k0 := (13408175658147/3906250000000000)
  k6 := (1382689221467957/125000000000000000)
  q := (175065701952152809457/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15324]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15324]

theorem width_15325 : mW 15325 = 445555379081060 := by
  have hu : mW 15325 ≤ 445555379081060 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15325 ≤ 445555379081059 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15325 : RowArithmetic 15325 (1087949698315413898733/1000000000000000000000000) (297773098027276381478653/500000000000000000000000) (1445579330965687/250000000000000000000000) where
  r0 := (131776899139/250000000000000000)
  k0 := (3432324982140619/1000000000000000000)
  k6 := (5530576434089993/500000000000000000)
  q := (87535707000057982053/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15325]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15325]

theorem width_15326 : mW 15326 = 445657145542961 := by
  have hu : mW 15326 ≤ 445657145542961 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15326 ≤ 445657145542960 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15326 : RowArithmetic 15326 (108792646591463778697/100000000000000000000000) (297768344556491757791629/500000000000000000000000) (2890668980818977/500000000000000000000000) where
  r0 := (527056007851/1000000000000000000)
  k0 := (3432157014979043/1000000000000000000)
  k6 := (1106079199993957/100000000000000000)
  q := (87538562930859220269/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15326]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15326]

theorem width_15327 : mW 15327 = 445758928606514 := by
  have hu : mW 15327 ≤ 445758928606514 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15327 ≤ 445758928606513 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15327 : RowArithmetic 15327 (543951619288068892009/500000000000000000000000) (595527183389941503469149/1000000000000000000000000) (5780358831304913/1000000000000000000000000) where
  r0 := (13175110689/25000000000000000)
  k0 := (68639781339879/20000000000000000)
  k6 := (2212086233403329/200000000000000000)
  q := (175082837536978478113/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15327]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15327]

theorem width_15328 : mW 15328 = 445860728273342 := by
  have hu : mW 15328 ≤ 445860728273342 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15328 ≤ 445860728273341 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15328 : RowArithmetic 15328 (135985002037308780937/125000000000000000000000) (119103535777035399278537/200000000000000000000000) (1444844983198287/250000000000000000000000) where
  r0 := (263476427841/500000000000000000)
  k0 := (34318211381849/10000000000000000)
  k6 := (11060070369405451/1000000000000000000)
  q := (87544274512957156609/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15328]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15328]

theorem width_15329 : mW 15329 = 445962544545071 := by
  have hu : mW 15329 ≤ 445962544545071 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15329 ≤ 445962544545070 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15329 : RowArithmetic 15329 (1087856799080191025689/1000000000000000000000000) (37219260974902531093977/62500000000000000000000) (5778401266032173/1000000000000000000000000) where
  r0 := (105380258443/200000000000000000)
  k0 := (686330645709639/200000000000000000)
  k6 := (11059709607100229/1000000000000000000)
  q := (175094260328544179267/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15329]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15329]

theorem width_15330 : mW 15330 = 446064377423327 := by
  have hu : mW 15330 ≤ 446064377423327 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15330 ≤ 446064377423326 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15330 : RowArithmetic 15330 (1087833586919856494557/1000000000000000000000000) (297749336764741249388277/500000000000000000000000) (231096913238061/40000000000000000000000) where
  r0 := (131712434289/250000000000000000)
  k0 := (3431485338076881/1000000000000000000)
  k6 := (11059348880095221/1000000000000000000)
  q := (87549985722443153349/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15330]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15330]

theorem width_15331 : mW 15331 = 446166226909733 := by
  have hu : mW 15331 ≤ 446166226909733 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15331 ≤ 446166226909732 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15331 : RowArithmetic 15331 (1087810379816024592393/1000000000000000000000000) (595489172678053544368251/1000000000000000000000000) (577644462748081/100000000000000000000000) where
  r0 := (65849773813/125000000000000000)
  k0 := (214457341673157/62500000000000000)
  k6 := (11058988188384671/1000000000000000000)
  q := (175105682374958922977/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15331]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15331]

theorem width_15332 : mW 15332 = 446268093005916 := by
  have hu : mW 15332 ≤ 446268093005916 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15332 ≤ 446268093005915 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15332 : RowArithmetic 15332 (271946794441813100937/250000000000000000000000) (595479673043904221683619/1000000000000000000000000) (5775466655549609/1000000000000000000000000) where
  r0 := (263373326129/500000000000000000)
  k0 := (1715574807314323/500000000000000000)
  k6 := (11058627531962823/1000000000000000000)
  q := (43777848279695063149/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15332]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15332]

theorem width_15333 : mW 15333 = 446369975713500 := by
  have hu : mW 15333 ≤ 446369975713500 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15333 ≤ 446369975713499 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15333 : RowArithmetic 15333 (1087763980772098574747/1000000000000000000000000) (297735087313392631599569/500000000000000000000000) (2887244457543783/500000000000000000000000) where
  r0 := (263347561207/500000000000000000)
  k0 := (1715490890820533/500000000000000000)
  k6 := (2764566727705981/250000000000000000)
  q := (175117103676368517079/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15333]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15333]

theorem width_15334 : mW 15334 = 446471875034110 := by
  have hu : mW 15334 ≤ 446471875034110 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15334 ≤ 446471875034109 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15334 : RowArithmetic 15334 (543870394414560966287/500000000000000000000000) (148865169356611872211651/250000000000000000000000) (5773511406024341/1000000000000000000000000) where
  r0 := (526643600971/1000000000000000000)
  k0 := (3430813967807327/1000000000000000000)
  k6 := (5528953162481111/500000000000000000)
  q := (175122814047741934977/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15334]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15334]

theorem width_15335 : mW 15335 = 446573790969372 := by
  have hu : mW 15335 ≤ 446573790969372 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15335 ≤ 446573790969371 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15335 : RowArithmetic 15335 (1087717601936881485877/1000000000000000000000000) (74431397680330204568219/125000000000000000000000) (721566766036201/125000000000000000000000) where
  r0 := (526592087927/1000000000000000000)
  k0 := (857661543280931/250000000000000000)
  k6 := (2764386443592991/250000000000000000)
  q := (175128524232918721869/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15335]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15335]

theorem width_15336 : mW 15336 = 446675723520911 := by
  have hu : mW 15336 ≤ 446675723520911 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15336 ≤ 446675723520910 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15336 : RowArithmetic 15336 (217538884018787422761/200000000000000000000000) (595441686675118718948979/1000000000000000000000000) (5771557081813079/1000000000000000000000000) where
  r0 := (526540583281/1000000000000000000)
  k0 := (343047839758981/100000000000000000)
  k6 := (5528592629523701/500000000000000000)
  q := (2736472409873704537/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15336]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15336]

theorem width_15337 : mW 15337 = 446777672690353 := by
  have hu : mW 15337 ≤ 446777672690353 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15337 ≤ 446777672690352 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15337 : RowArithmetic 15337 (16994863176544513699/15625000000000000000000) (595432193123629615023957/1000000000000000000000000) (5770580266524481/1000000000000000000000000) where
  r0 := (52648908703/100000000000000000)
  k0 := (1715155320599311/500000000000000000)
  k6 := (5528412389491393/500000000000000000)
  q := (43784986011188812529/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15337]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15337]

theorem width_15338 : mW 15338 = 446879638479322 := by
  have hu : mW 15338 ≤ 446879638479322 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15338 ≤ 446879638479321 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15338 : RowArithmetic 15338 (1087648071550178048843/1000000000000000000000000) (119084540157585099518789/200000000000000000000000) (2884801841176797/500000000000000000000000) where
  r0 := (526437599173/1000000000000000000)
  k0 := (3430142903949711/1000000000000000000)
  k6 := (1105646433417237/100000000000000000)
  q := (175145653671451407787/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15338]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15338]

theorem width_15339 : mW 15339 = 446981620889444 := by
  have hu : mW 15339 ≤ 446981620889444 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15339 ≤ 446981620889443 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15339 : RowArithmetic 15339 (1087624904846485740849/1000000000000000000000000) (148853302416939354786839/250000000000000000000000) (5768627329230199/1000000000000000000000000) where
  r0 := (526386119707/1000000000000000000)
  k0 := (3429975185836109/1000000000000000000)
  k6 := (1382012990576301/125000000000000000)
  q := (10946960194501485443/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15339]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15339]

theorem width_15340 : mW 15340 = 447083619922345 := by
  have hu : mW 15340 ≤ 447083619922345 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15340 ≤ 447083619922344 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15340 : RowArithmetic 15340 (16993777237286462323/15625000000000000000000) (297701859881438281159541/500000000000000000000000) (5767651207084101/1000000000000000000000000) where
  r0 := (52633464863/100000000000000000)
  k0 := (342980748685411/100000000000000000)
  k6 := (5527871775145577/500000000000000000)
  q := (87578536183245264379/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15340]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15340]

theorem width_15341 : mW 15341 = 447185635579651 := by
  have hu : mW 15341 ≤ 447185635579651 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15341 ≤ 447185635579650 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15341 : RowArithmetic 15341 (43503143462731350127/40000000000000000000000) (29769711553651711036317/50000000000000000000000) (1153335063169027/200000000000000000000000) where
  r0 := (263141592971/500000000000000000)
  k0 := (1714819903503259/500000000000000000)
  k6 := (2211076642241773/200000000000000000)
  q := (175162781434869890571/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15341]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15341]

theorem width_15342 : mW 15342 = 447287667862986 := by
  have hu : mW 15342 ≤ 447287667862986 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15342 ≤ 447287667862985 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15342 : RowArithmetic 15342 (1087555434990899606979/1000000000000000000000000) (595384743597981687105687/1000000000000000000000000) (5765699655443187/1000000000000000000000000) where
  r0 := (526231731639/1000000000000000000)
  k0 := (1714736073141553/500000000000000000)
  k6 := (11055022907357801/1000000000000000000)
  q := (35033698063436009467/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15342]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15342]

theorem width_15343 : mW 15343 = 447389716773977 := by
  have hu : mW 15343 ≤ 447389716773977 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15343 ≤ 447389716773976 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15343 : RowArithmetic 15343 (108753228845274401591/100000000000000000000000) (595375257337470378359757/1000000000000000000000000) (1441181056452033/250000000000000000000000) where
  r0 := (13154507143/25000000000000000)
  k0 := (3429304504683421/1000000000000000000)
  k6 := (11054662638732219/1000000000000000000)
  q := (87587099506719595447/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15343]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15343]

theorem width_15344 : mW 15344 = 447491782314249 := by
  have hu : mW 15344 ≤ 447491782314249 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15344 ≤ 447491782314248 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15344 : RowArithmetic 15344 (1087509146952381057061/1000000000000000000000000) (595365772291251763444791/1000000000000000000000000) (1152749805373979/200000000000000000000000) where
  r0 := (526128848183/1000000000000000000)
  k0 := (2743309505763/800000000000000)
  k6 := (552715120266319/50000000000000000)
  q := (87589953761832755063/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15344]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15344]

theorem width_15345 : mW 15345 = 447593864485429 := by
  have hu : mW 15345 ≤ 447593864485429 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15345 ≤ 447593864485428 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15345 : RowArithmetic 15345 (543743005244187322339/500000000000000000000000) (595356288459077406107881/1000000000000000000000000) (2881387029279203/500000000000000000000000) where
  r0 := (263038709513/500000000000000000)
  k0 := (1714484639420189/500000000000000000)
  k6 := (11053942207134547/1000000000000000000)
  q := (43796403961969297737/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15345]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15345]

theorem width_15346 : mW 15346 = 447695963289141 := by
  have hu : mW 15346 ≤ 447695963289141 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15346 ≤ 447695963289140 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15346 : RowArithmetic 15346 (1087462879059290246267/1000000000000000000000000) (595346805840698901501061/1000000000000000000000000) (1152359864160731/200000000000000000000000) where
  r0 := (526025998247/1000000000000000000)
  k0 := (3428801694589591/1000000000000000000)
  k6 := (11053582044150983/1000000000000000000)
  q := (21898915498261552039/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15346]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15346]

theorem width_15347 : mW 15347 = 447798078727012 := by
  have hu : mW 15347 ≤ 447798078727012 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15347 ≤ 447798078727011 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15347 : RowArithmetic 15347 (217487950532738564623/200000000000000000000000) (74417165554483490957653/125000000000000000000000) (2880412406767813/500000000000000000000000) where
  r0 := (131493646461/250000000000000000)
  k0 := (3428634129447673/1000000000000000000)
  k6 := (345413184886561/31250000000000000)
  q := (175197031938329366209/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15347]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15347]

theorem width_15348 : mW 15348 = 447900210800668 := by
  have hu : mW 15348 ≤ 447900210800668 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15348 ≤ 447900210800667 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15348 : RowArithmetic 15348 (543708315650074101497/500000000000000000000000) (148831961061084055888427/250000000000000000000000) (5759850536684337/1000000000000000000000000) where
  r0 := (65740397727/125000000000000000)
  k0 := (1714233291707083/500000000000000000)
  k6 := (11052861823785719/1000000000000000000)
  q := (43800684926151554417/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15348]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15348]

theorem width_15349 : mW 15349 = 448002359511735 := by
  have hu : mW 15349 ≤ 448002359511735 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15349 ≤ 448002359511734 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15349 : RowArithmetic 15349 (1087393514967222736643/1000000000000000000000000) (148829591316463913808187/250000000000000000000000) (1439719122544959/250000000000000000000000) where
  r0 := (6573397327/12500000000000000)
  k0 := (857074764120523/250000000000000000)
  k6 := (11052501766392553/1000000000000000000)
  q := (87604223642470572379/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15349]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15349]

theorem width_15350 : mW 15350 = 448104524861838 := by
  have hu : mW 15350 ≤ 448104524861838 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15350 ≤ 448104524861837 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15350 : RowArithmetic 15350 (217474080732696728003/200000000000000000000000) (595308887500178078872007/1000000000000000000000000) (575790267395221/100000000000000000000000) where
  r0 := (262910199437/500000000000000000)
  k0 := (3428131548647733/1000000000000000000)
  k6 := (5526070872092361/500000000000000000)
  q := (43803538669838079647/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15350]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15350]

theorem width_15351 : mW 15351 = 448206706852605 := by
  have hu : mW 15351 ≤ 448206706852605 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15351 ≤ 448206706852604 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15351 : RowArithmetic 15351 (543673648693748811969/500000000000000000000000) (18603106592095481930433/31250000000000000000000) (1439232271982883/250000000000000000000000) where
  r0 := (525769019957/1000000000000000000)
  k0 := (856991014977657/250000000000000000)
  k6 := (5525890878578247/500000000000000000)
  q := (87609930943928953653/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15351]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15351]

theorem width_15352 : mW 15352 = 448308905485660 := by
  have hu : mW 15352 ≤ 448308905485660 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15352 ≤ 448308905485659 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15352 : RowArithmetic 15352 (1087324196137833291429/1000000000000000000000000) (595289935606239747217901/1000000000000000000000000) (1438988933011989/250000000000000000000000) where
  r0 := (525717649407/1000000000000000000)
  k0 := (214237286891691/62500000000000000)
  k6 := (11051421805302143/1000000000000000000)
  q := (175225568910476076103/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15352]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15352]

theorem width_15353 : mW 15353 = 448411120762631 := by
  have hu : mW 15353 ≤ 448411120762631 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15353 ≤ 448411120762630 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15353 : RowArithmetic 15353 (543650549956529199023/500000000000000000000000) (74410057684685397955301/125000000000000000000000) (5754982606231609/1000000000000000000000000) where
  r0 := (262833143611/500000000000000000)
  k0 := (685525827942659/200000000000000000)
  k6 := (11051061888615939/1000000000000000000)
  q := (175231275747224987211/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15353]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15353]

theorem width_15354 : mW 15354 = 448513352685143 := by
  have hu : mW 15354 ≤ 448513352685143 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15354 ≤ 448513352685142 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15354 : RowArithmetic 15354 (543639004355871124019/500000000000000000000000) (297635494280268926275593/500000000000000000000000) (1438502427603171/250000000000000000000000) where
  r0 := (525614933399/1000000000000000000)
  k0 := (1713730854121181/500000000000000000)
  k6 := (11050702007092157/1000000000000000000)
  q := (87618491199061399953/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15354]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15354]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 15280 then ⟨(108900041932504406257/100000000000000000000000), (297987636831313137788647/500000000000000000000000), (5826629780221237/1000000000000000000000000)⟩ else
  if n = 15281 then ⟨(544488478809346648137/500000000000000000000000), (595965711627800721896601/1000000000000000000000000), (5825639909473269/1000000000000000000000000)⟩ else
  if n = 15282 then ⟨(21779070020802844253/20000000000000000000000), (297978075411404883706717/500000000000000000000000), (5824650273816819/1000000000000000000000000)⟩ else
  if n = 15283 then ⟨(1088930049587923563619/1000000000000000000000000), (595946591247400526431343/1000000000000000000000000), (1455915218295051/250000000000000000000000)⟩ else
  if n = 15284 then ⟨(544453301630285143527/500000000000000000000000), (37246064556332517000547/62500000000000000000000), (1455667926872939/250000000000000000000000)⟩ else
  if n = 15285 then ⟨(217776632411323241859/200000000000000000000000), (595927475784316294520507/1000000000000000000000000), (5821682776679847/1000000000000000000000000)⟩ else
  if n = 15286 then ⟨(136107465746824417799/125000000000000000000000), (595917919896135986927003/1000000000000000000000000), (5820694080672863/1000000000000000000000000)⟩ else
  if n = 15287 then ⟨(1088836295013042586087/1000000000000000000000000), (595908365236526757993287/1000000000000000000000000), (581970561939923/100000000000000000000000)⟩ else
  if n = 15288 then ⟨(544406434585246337471/500000000000000000000000), (595898811805236194338229/1000000000000000000000000), (5818717392787377/1000000000000000000000000)⟩ else
  if n = 15289 then ⟨(544394724222740966001/500000000000000000000000), (297944629801005912293869/500000000000000000000000), (2908864700382899/500000000000000000000000)⟩ else
  if n = 15290 then ⟨(1088766032836545813859/1000000000000000000000000), (119175941725320262191817/200000000000000000000000), (2908370821631481/500000000000000000000000)⟩ else
  if n = 15291 then ⟨(1088742622342221364813/1000000000000000000000000), (148967539719688103485397/250000000000000000000000), (2907877060103703/500000000000000000000000)⟩ else
  if n = 15292 then ⟨(108871921696104616427/100000000000000000000000), (595860610358212943620069/1000000000000000000000000), (1453691707881923/250000000000000000000000)⟩ else
  if n = 15293 then ⟨(544347908345778638269/500000000000000000000000), (148962765766182678850173/250000000000000000000000), (1453444944288093/250000000000000000000000)⟩ else
  if n = 15294 then ⟨(544336210766146850763/500000000000000000000000), (595841516998053790312277/1000000000000000000000000), (1453198239252519/250000000000000000000000)⟩ else
  if n = 15295 then ⟨(544324515740896961901/500000000000000000000000), (297915986078965042183301/500000000000000000000000), (5811806371029423/1000000000000000000000000)⟩ else
  if n = 15296 then ⟨(217725129307719392619/200000000000000000000000), (595822428544107741522947/1000000000000000000000000), (290541000956953/50000000000000000000000)⟩ else
  if n = 15297 then ⟨(1088602266701243072939/1000000000000000000000000), (595812886156334882960951/1000000000000000000000000), (2904916950633843/500000000000000000000000)⟩ else
  if n = 15298 then ⟨(17009045187004255341/15625000000000000000000), (5958033449943597516877/10000000000000000000000), (5808848017344001/1000000000000000000000000)⟩ else
  if n = 15299 then ⟨(217711104467645078527/200000000000000000000000), (29789690252896533042039/50000000000000000000000), (2903931183648367/500000000000000000000000)⟩ else
  if n = 15300 then ⟨(544266078904822214783/500000000000000000000000), (119156853269359198739907/200000000000000000000000), (5806876951054677/1000000000000000000000000)⟩ else
  if n = 15301 then ⟨(1088508798381070444507/1000000000000000000000000), (29788736443035209299339/50000000000000000000000), (1451472942136647/250000000000000000000000)⟩ else
  if n = 15302 then ⟨(1088485444051046359207/1000000000000000000000000), (297882596299701850403731/500000000000000000000000), (2902453409850651/500000000000000000000000)⟩ else
  if n = 15303 then ⟨(272115523704528732607/250000000000000000000000), (297877828781321600539957/500000000000000000000000), (2901961052223827/500000000000000000000000)⟩ else
  if n = 15304 then ⟨(1088438750680819448071/1000000000000000000000000), (37234132734385707292229/62500000000000000000000), (580293762271451/100000000000000000000000)⟩ else
  if n = 15305 then ⟨(217683082327540816663/200000000000000000000000), (119147318232347350399053/200000000000000000000000), (5801953374430771/1000000000000000000000000)⟩ else
  if n = 15306 then ⟨(1088392077687313191181/1000000000000000000000000), (595727059797088319808357/1000000000000000000000000), (5800969359525357/1000000000000000000000000)⟩ else
  if n = 15307 then ⟨(1088368748828191659073/1000000000000000000000000), (119143505931194981180631/200000000000000000000000), (5799985577927213/1000000000000000000000000)⟩ else
  if n = 15308 then ⟨(27208635626472131363/25000000000000000000000), (7446350009226817829521/12500000000000000000000), (2899501014782661/500000000000000000000000)⟩ else
  if n = 15309 then ⟨(544161053188969790337/500000000000000000000000), (595698473043348913030011/1000000000000000000000000), (181188084824021/31250000000000000000000)⟩ else
  if n = 15310 then ⟨(217659758556780293661/200000000000000000000000), (29784447328566721251147/50000000000000000000000), (2898517816133151/500000000000000000000000)⟩ else
  if n = 15311 then ⟨(544137742137658791917/500000000000000000000000), (595679421321851116593089/1000000000000000000000000), (5796052783187251/1000000000000000000000000)⟩ else
  if n = 15312 then ⟨(1088252180850735820267/1000000000000000000000000), (297834948647324104509493/500000000000000000000000), (2897535083530307/500000000000000000000000)⟩ else
  if n = 15313 then ⟨(1088228882508704253621/1000000000000000000000000), (297830187244737522619247/500000000000000000000000), (5794087783815497/1000000000000000000000000)⟩ else
  if n = 15314 then ⟨(217641117849554159227/200000000000000000000000), (119130170581216189353989/200000000000000000000000), (5793105633381009/1000000000000000000000000)⟩ else
  if n = 15315 then ⟨(1088182301066485626821/1000000000000000000000000), (297820666272107657015981/500000000000000000000000), (5792123715686351/1000000000000000000000000)⟩ else
  if n = 15316 then ⟨(136019877245424671451/125000000000000000000000), (9306747084431683110261/15625000000000000000000), (5791142030660671/1000000000000000000000000)⟩ else
  if n = 15317 then ⟨(1088135739937056228293/1000000000000000000000000), (119124459096813536316937/200000000000000000000000), (1158032115646637/200000000000000000000000)⟩ else
  if n = 15318 then ⟨(1088112466986013617643/1000000000000000000000000), (297806389392642439133043/500000000000000000000000), (2894589679166581/500000000000000000000000)⟩ else
  if n = 15319 then ⟨(108808919910881975603/100000000000000000000000), (297801631653514516794193/500000000000000000000000), (723524796361229/125000000000000000000000)⟩ else
  if n = 15320 then ⟨(1088065936304026429761/1000000000000000000000000), (37224609315565617599531/62500000000000000000000), (5787217615832491/1000000000000000000000000)⟩ else
  if n = 15321 then ⟨(1088042678570186300291/1000000000000000000000000), (297792118005548689766989/500000000000000000000000), (231449483723619/40000000000000000000000)⟩ else
  if n = 15322 then ⟨(544009712952925586291/500000000000000000000000), (595574724192921337931617/1000000000000000000000000), (723157100324137/125000000000000000000000)⟩ else
  if n = 15323 then ⟨(135999522288696888953/125000000000000000000000), (595565213594271877476617/1000000000000000000000000), (1446069186067439/250000000000000000000000)⟩ else
  if n = 15324 then ⟨(1087972935779911325941/1000000000000000000000000), (595555704214898952951263/1000000000000000000000000), (2891648459024917/500000000000000000000000)⟩ else
  if n = 15325 then ⟨(1087949698315413898733/1000000000000000000000000), (297773098027276381478653/500000000000000000000000), (1445579330965687/250000000000000000000000)⟩ else
  if n = 15326 then ⟨(108792646591463778697/100000000000000000000000), (297768344556491757791629/500000000000000000000000), (2890668980818977/500000000000000000000000)⟩ else
  if n = 15327 then ⟨(543951619288068892009/500000000000000000000000), (595527183389941503469149/1000000000000000000000000), (5780358831304913/1000000000000000000000000)⟩ else
  if n = 15328 then ⟨(135985002037308780937/125000000000000000000000), (119103535777035399278537/200000000000000000000000), (1444844983198287/250000000000000000000000)⟩ else
  if n = 15329 then ⟨(1087856799080191025689/1000000000000000000000000), (37219260974902531093977/62500000000000000000000), (5778401266032173/1000000000000000000000000)⟩ else
  if n = 15330 then ⟨(1087833586919856494557/1000000000000000000000000), (297749336764741249388277/500000000000000000000000), (231096913238061/40000000000000000000000)⟩ else
  if n = 15331 then ⟨(1087810379816024592393/1000000000000000000000000), (595489172678053544368251/1000000000000000000000000), (577644462748081/100000000000000000000000)⟩ else
  if n = 15332 then ⟨(271946794441813100937/250000000000000000000000), (595479673043904221683619/1000000000000000000000000), (5775466655549609/1000000000000000000000000)⟩ else
  if n = 15333 then ⟨(1087763980772098574747/1000000000000000000000000), (297735087313392631599569/500000000000000000000000), (2887244457543783/500000000000000000000000)⟩ else
  if n = 15334 then ⟨(543870394414560966287/500000000000000000000000), (148865169356611872211651/250000000000000000000000), (5773511406024341/1000000000000000000000000)⟩ else
  if n = 15335 then ⟨(1087717601936881485877/1000000000000000000000000), (74431397680330204568219/125000000000000000000000), (721566766036201/125000000000000000000000)⟩ else
  if n = 15336 then ⟨(217538884018787422761/200000000000000000000000), (595441686675118718948979/1000000000000000000000000), (5771557081813079/1000000000000000000000000)⟩ else
  if n = 15337 then ⟨(16994863176544513699/15625000000000000000000), (595432193123629615023957/1000000000000000000000000), (5770580266524481/1000000000000000000000000)⟩ else
  if n = 15338 then ⟨(1087648071550178048843/1000000000000000000000000), (119084540157585099518789/200000000000000000000000), (2884801841176797/500000000000000000000000)⟩ else
  if n = 15339 then ⟨(1087624904846485740849/1000000000000000000000000), (148853302416939354786839/250000000000000000000000), (5768627329230199/1000000000000000000000000)⟩ else
  if n = 15340 then ⟨(16993777237286462323/15625000000000000000000), (297701859881438281159541/500000000000000000000000), (5767651207084101/1000000000000000000000000)⟩ else
  if n = 15341 then ⟨(43503143462731350127/40000000000000000000000), (29769711553651711036317/50000000000000000000000), (1153335063169027/200000000000000000000000)⟩ else
  if n = 15342 then ⟨(1087555434990899606979/1000000000000000000000000), (595384743597981687105687/1000000000000000000000000), (5765699655443187/1000000000000000000000000)⟩ else
  if n = 15343 then ⟨(108753228845274401591/100000000000000000000000), (595375257337470378359757/1000000000000000000000000), (1441181056452033/250000000000000000000000)⟩ else
  if n = 15344 then ⟨(1087509146952381057061/1000000000000000000000000), (595365772291251763444791/1000000000000000000000000), (1152749805373979/200000000000000000000000)⟩ else
  if n = 15345 then ⟨(543743005244187322339/500000000000000000000000), (595356288459077406107881/1000000000000000000000000), (2881387029279203/500000000000000000000000)⟩ else
  if n = 15346 then ⟨(1087462879059290246267/1000000000000000000000000), (595346805840698901501061/1000000000000000000000000), (1152359864160731/200000000000000000000000)⟩ else
  if n = 15347 then ⟨(217487950532738564623/200000000000000000000000), (74417165554483490957653/125000000000000000000000), (2880412406767813/500000000000000000000000)⟩ else
  if n = 15348 then ⟨(543708315650074101497/500000000000000000000000), (148831961061084055888427/250000000000000000000000), (5759850536684337/1000000000000000000000000)⟩ else
  if n = 15349 then ⟨(1087393514967222736643/1000000000000000000000000), (148829591316463913808187/250000000000000000000000), (1439719122544959/250000000000000000000000)⟩ else
  if n = 15350 then ⟨(217474080732696728003/200000000000000000000000), (595308887500178078872007/1000000000000000000000000), (575790267395221/100000000000000000000000)⟩ else
  if n = 15351 then ⟨(543673648693748811969/500000000000000000000000), (18603106592095481930433/31250000000000000000000), (1439232271982883/250000000000000000000000)⟩ else
  if n = 15352 then ⟨(1087324196137833291429/1000000000000000000000000), (595289935606239747217901/1000000000000000000000000), (1438988933011989/250000000000000000000000)⟩ else
  if n = 15353 then ⟨(543650549956529199023/500000000000000000000000), (74410057684685397955301/125000000000000000000000), (5754982606231609/1000000000000000000000000)⟩ else
  ⟨(543639004355871124019/500000000000000000000000), (297635494280268926275593/500000000000000000000000), (1438502427603171/250000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15280 ≤ n) (hb : n ≤ 15354) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15280
  · exact row_15281
  · exact row_15282
  · exact row_15283
  · exact row_15284
  · exact row_15285
  · exact row_15286
  · exact row_15287
  · exact row_15288
  · exact row_15289
  · exact row_15290
  · exact row_15291
  · exact row_15292
  · exact row_15293
  · exact row_15294
  · exact row_15295
  · exact row_15296
  · exact row_15297
  · exact row_15298
  · exact row_15299
  · exact row_15300
  · exact row_15301
  · exact row_15302
  · exact row_15303
  · exact row_15304
  · exact row_15305
  · exact row_15306
  · exact row_15307
  · exact row_15308
  · exact row_15309
  · exact row_15310
  · exact row_15311
  · exact row_15312
  · exact row_15313
  · exact row_15314
  · exact row_15315
  · exact row_15316
  · exact row_15317
  · exact row_15318
  · exact row_15319
  · exact row_15320
  · exact row_15321
  · exact row_15322
  · exact row_15323
  · exact row_15324
  · exact row_15325
  · exact row_15326
  · exact row_15327
  · exact row_15328
  · exact row_15329
  · exact row_15330
  · exact row_15331
  · exact row_15332
  · exact row_15333
  · exact row_15334
  · exact row_15335
  · exact row_15336
  · exact row_15337
  · exact row_15338
  · exact row_15339
  · exact row_15340
  · exact row_15341
  · exact row_15342
  · exact row_15343
  · exact row_15344
  · exact row_15345
  · exact row_15346
  · exact row_15347
  · exact row_15348
  · exact row_15349
  · exact row_15350
  · exact row_15351
  · exact row_15352
  · exact row_15353
  · exact row_15354

end BstLean.Part271.R3.Rows15280
