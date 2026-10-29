import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 16130–16199. -/
namespace BstLean.Part271.R3.Rows16130
open Real BstLean.Part130 BstLean.Part227

theorem width_16130 : mW 16130 = 532991503420381 := by
  have hu : mW 16130 ≤ 532991503420381 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16130 ≤ 532991503420380 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16130 : RowArithmetic 16130 (535384498843397773129/500000000000000000000000) (588266965136986741471591/1000000000000000000000000) (5063291068348033/1000000000000000000000000) where
  r0 := (12203613863/25000000000000000)
  k0 := (206439598399133/62500000000000000)
  k6 := (10781605883098997/1000000000000000000)
  q := (17961069010501574263/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16130]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16130]

theorem width_16131 : mW 16131 = 533107164600278 := by
  have hu : mW 16131 ≤ 533107164600278 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16131 ≤ 533107164600277 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16131 : RowArithmetic 16131 (267687353421116030309/250000000000000000000000) (73532295499768833904971/125000000000000000000000) (2531238823351103/500000000000000000000000) where
  r0 := (244049581659/500000000000000000)
  k0 := (1651440000435779/500000000000000000)
  k6 := (5390635844454111/500000000000000000)
  q := (11226016101003953219/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16131]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16131]

theorem width_16132 : mW 16132 = 533222843706859 := by
  have hu : mW 16132 ≤ 533222843706859 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16132 ≤ 533222843706858 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16132 : RowArithmetic 16132 (1070729833729643883147/1000000000000000000000000) (588249763897608358499781/1000000000000000000000000) (5061664407761761/1000000000000000000000000) where
  r0 := (9761075583/20000000000000000)
  k0 := (330272644401599/100000000000000000)
  k6 := (10780937525792271/1000000000000000000)
  q := (89810912477270823017/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16132]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16132]

theorem width_16133 : mW 16133 = 533338540741792 := by
  have hu : mW 16133 ≤ 533338540741792 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16133 ≤ 533338540741791 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16133 : RowArithmetic 16133 (1070710257821239046333/1000000000000000000000000) (294120582417579724896811/500000000000000000000000) (632606418934249/125000000000000000000000) where
  r0 := (97601680403/200000000000000000)
  k0 := (3302572903818363/1000000000000000000)
  k6 := (10780603393746327/1000000000000000000)
  q := (89813696060233485973/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16133]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16133]

theorem width_16134 : mW 16134 = 533454255706745 := by
  have hu : mW 16134 ≤ 533454255706745 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16134 ≤ 533454255706744 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16134 : RowArithmetic 16134 (1070690685958154205081/1000000000000000000000000) (7352907085132545359139/12500000000000000000000) (158126202430819/31250000000000000000000) where
  r0 := (487963031911/1000000000000000000)
  k0 := (1651209690137117/500000000000000000)
  k6 := (5390134646382789/500000000000000000)
  q := (89816479556927636241/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16134]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16134]

theorem width_16135 : mW 16135 = 533569988603383 := by
  have hu : mW 16135 ≤ 533569988603383 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16135 ≤ 533569988603382 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16135 : RowArithmetic 16135 (1070671118139295102243/1000000000000000000000000) (147055992455935152935097/250000000000000000000000) (5059225786645769/1000000000000000000000000) where
  r0 := (121979417209/250000000000000000)
  k0 := (3302265873379157/1000000000000000000)
  k6 := (10779935222845209/1000000000000000000)
  q := (89819262967361294197/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16135]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16135]

theorem width_16136 : mW 16136 = 533685739433375 := by
  have hu : mW 16136 ≤ 533685739433375 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16136 ≤ 533685739433374 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16136 : RowArithmetic 16136 (214130310872713366897/200000000000000000000000) (588215373874370213851433/1000000000000000000000000) (316150829875001/62500000000000000000000) where
  r0 := (48787231279/100000000000000000)
  k0 := (3302112383135453/1000000000000000000)
  k6 := (10779601183980407/1000000000000000000)
  q := (701734736652675617/3906250000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16136]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16136]

theorem width_16137 : mW 16137 = 533801508198388 := by
  have hu : mW 16137 ≤ 533801508198388 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16137 ≤ 533801508198387 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16137 : RowArithmetic 16137 (267657998657468847609/250000000000000000000000) (588206778962292322663911/1000000000000000000000000) (202304038071853/40000000000000000000000) where
  r0 := (48782696377/100000000000000000)
  k0 := (3301958909535293/1000000000000000000)
  k6 := (10779267176166363/1000000000000000000)
  q := (179649659058958416939/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16137]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16137]

theorem width_16138 : mW 16138 = 533917294900089 := by
  have hu : mW 16138 ≤ 533917294900089 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16138 ≤ 533917294900088 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16138 : RowArithmetic 16138 (1070612438937127137619/1000000000000000000000000) (294099092543653384233103/500000000000000000000000) (316049300498881/62500000000000000000000) where
  r0 := (19511264871/40000000000000000)
  k0 := (3301805452577613/1000000000000000000)
  k6 := (2155786639879653/200000000000000000)
  q := (179655225362358998657/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16138]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16138]

theorem width_16139 : mW 16139 = 534033099540145 := by
  have hu : mW 16139 ≤ 534033099540145 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16139 ≤ 534033099540144 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16139 : RowArithmetic 16139 (535296443642114411143/500000000000000000000000) (588189592249213527646427/1000000000000000000000000) (2527988423252371/500000000000000000000000) where
  r0 := (121934071701/250000000000000000)
  k0 := (3301652012261347/1000000000000000000)
  k6 := (1347324906708913/125000000000000000)
  q := (179660791493302733919/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16139]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16139]

theorem width_16140 : mW 16140 = 534148922120224 := by
  have hu : mW 16140 ≤ 534148922120224 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16140 ≤ 534148922120223 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16140 : RowArithmetic 16140 (535286669835043656721/500000000000000000000000) (588181000447812620693787/1000000000000000000000000) (5055165067311691/1000000000000000000000000) where
  r0 := (97538191771/200000000000000000)
  k0 := (103171830893189/31250000000000000)
  k6 := (168410395921573/15625000000000000)
  q := (8983317872590282553/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16140]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16140]

theorem width_16141 : mW 16141 = 534264762641992 := by
  have hu : mW 16141 ≤ 534264762641992 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16141 ≤ 534264762641991 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16141 : RowArithmetic 16141 (1070553796093610370269/1000000000000000000000000) (117634481936580821674871/200000000000000000000000) (1010870694070081/200000000000000000000000) where
  r0 := (487645637927/1000000000000000000)
  k0 := (3301345181538649/1000000000000000000)
  k6 := (10777931455321561/1000000000000000000)
  q := (17967192323788377593/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16141]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16141]

theorem width_16142 : mW 16142 = 534380621107118 := by
  have hu : mW 16142 ≤ 534380621107118 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16142 ≤ 534380621107117 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16142 : RowArithmetic 16142 (214106851310741072589/200000000000000000000000) (147040954988572027945713/250000000000000000000000) (2526771027784169/500000000000000000000000) where
  r0 := (487600324017/1000000000000000000)
  k0 := (1650595895561657/500000000000000000)
  k6 := (10777597602689167/1000000000000000000)
  q := (22459686106444141487/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16142]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16142]

theorem width_16143 : mW 16143 = 534496497517269 := by
  have hu : mW 16143 ≤ 534496497517269 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16143 ≤ 534496497517268 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16143 : RowArithmetic 16143 (267628680262320137871/250000000000000000000000) (58815523126176475668557/100000000000000000000000) (631591352864123/125000000000000000000000) where
  r0 := (3900440137/8000000000000000)
  k0 := (3301038417338361/1000000000000000000)
  k6 := (10777263781078683/1000000000000000000)
  q := (44920763573207434961/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16143]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16143]

theorem width_16144 : mW 16144 = 534612391874113 := by
  have hu : mW 16144 ≤ 534612391874113 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16144 ≤ 534612391874112 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16144 : RowArithmetic 16144 (214099037915848863669/200000000000000000000000) (294073321802567156680277/500000000000000000000000) (2525959886165921/500000000000000000000000) where
  r0 := (487509717249/1000000000000000000)
  k0 := (1650442530089669/500000000000000000)
  k6 := (5388464995242653/500000000000000000)
  q := (179688619561729618181/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16144]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16144]

theorem width_16145 : mW 16145 = 534728304179317 := by
  have hu : mW 16145 ≤ 534728304179317 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16145 ≤ 534728304179316 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16145 : RowArithmetic 16145 (1070475662142505679409/1000000000000000000000000) (588138056984197053561131/1000000000000000000000000) (1262777225943111/250000000000000000000000) where
  r0 := (487464424387/1000000000000000000)
  k0 := (3300731719641791/1000000000000000000)
  k6 := (10776596230904233/1000000000000000000)
  q := (179694184658268782831/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16145]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16145]

theorem width_16146 : mW 16146 = 534844234434548 := by
  have hu : mW 16146 ≤ 534844234434548 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16146 ≤ 534844234434547 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16146 : RowArithmetic 16146 (214091227747594805619/200000000000000000000000) (36758091962422077909603/62500000000000000000000) (2525149108591169/500000000000000000000000) where
  r0 := (243709569269/500000000000000000)
  k0 := (66011567914493/20000000000000000)
  k6 := (10776262502330661/1000000000000000000)
  q := (89849874791231623619/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16146]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16146]

theorem width_16147 : mW 16147 = 534960182641475 := by
  have hu : mW 16147 ≤ 534960182641475 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16147 ≤ 534960182641474 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16147 : RowArithmetic 16147 (13380457742056982811/12500000000000000000000) (147030221712150828291321/250000000000000000000000) (5049487712509073/1000000000000000000000000) where
  r0 := (487373859701/1000000000000000000)
  k0 := (1650212544213423/500000000000000000)
  k6 := (1077592880475979/100000000000000000)
  q := (179705314334329022369/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16147]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16147]

theorem width_16148 : mW 16148 = 535076148801766 := by
  have hu : mW 16148 ≤ 535076148801766 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16148 ≤ 535076148801765 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16148 : RowArithmetic 16148 (267604276005292340811/250000000000000000000000) (294056151666773846031247/500000000000000000000000) (2524338694850113/500000000000000000000000) where
  r0 := (487328587873/1000000000000000000)
  k0 := (3300271797740537/1000000000000000000)
  k6 := (538779756909341/50000000000000000)
  q := (17971087891388211671/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16148]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16148]

theorem width_16149 : mW 16149 = 535192132917088 := by
  have hu : mW 16149 ≤ 535192132917088 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16149 ≤ 535192132917087 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16149 : RowArithmetic 16149 (1070397592706716769043/1000000000000000000000000) (147025930213346715852819/250000000000000000000000) (5047867248703403/1000000000000000000000000) where
  r0 := (243641661527/500000000000000000)
  k0 := (3300118523668037/1000000000000000000)
  k6 := (10775261502606953/1000000000000000000)
  q := (179716443321138536269/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16149]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16149]

theorem width_16150 : mW 16150 = 535308134989109 := by
  have hu : mW 16150 ≤ 535308134989109 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16150 ≤ 535308134989108 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16150 : RowArithmetic 16150 (214075617084022298023/200000000000000000000000) (147023784851980327594253/250000000000000000000000) (252352864473311/50000000000000000000000) where
  r0 := (243619032621/500000000000000000)
  k0 := (3299965266204889/1000000000000000000)
  k6 := (1077492789801539/100000000000000000)
  q := (179722007556114284577/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16150]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16150]

theorem width_16151 : mW 16151 = 535424155019497 := by
  have hu : mW 16151 ≤ 535424155019497 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16151 ≤ 535424155019496 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16151 : RowArithmetic 16151 (535179291080132275681/500000000000000000000000) (294043279498475850142143/500000000000000000000000) (504624751193631/100000000000000000000000) where
  r0 := (97438562887/200000000000000000)
  k0 := (1649906012673317/500000000000000000)
  k6 := (2154918864881467/200000000000000000)
  q := (35945514323765072537/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16151]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16151]

theorem width_16152 : mW 16152 = 535540193009920 := by
  have hu : mW 16152 ≤ 535540193009920 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16152 ≤ 535540193009919 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16152 : RowArithmetic 16152 (535169541463043677291/500000000000000000000000) (294038989810139311286873/500000000000000000000000) (2522718958030663/500000000000000000000000) where
  r0 := (487147570631/1000000000000000000)
  k0 := (824914700272203/250000000000000000)
  k6 := (1346782597722249/125000000000000000)
  q := (44933283877321942293/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16152]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16152]

theorem width_16153 : mW 16153 = 535656248962046 := by
  have hu : mW 16153 ≤ 535656248962046 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16153 ≤ 535656248962045 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16153 : RowArithmetic 16153 (133789948464561459787/125000000000000000000000) (294034700638851406276473/500000000000000000000000) (252231425089447/50000000000000000000000) where
  r0 := (48710233383/100000000000000000)
  k0 := (659901118686747/200000000000000000)
  k6 := (5386963635061283/500000000000000000)
  q := (22467337403439687517/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16153]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16153]

theorem width_16154 : mW 16154 = 535772322877543 := by
  have hu : mW 16154 ≤ 535772322877543 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16154 ≤ 535772322877542 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16154 : RowArithmetic 16154 (535150048265194838793/500000000000000000000000) (294030411984512477088309/500000000000000000000000) (1260954817266711/250000000000000000000000) where
  r0 := (48705710403/100000000000000000)
  k0 := (3299352402376943/1000000000000000000)
  k6 := (1346699223679533/125000000000000000)
  q := (179744262773530549203/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16154]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16154]

theorem width_16155 : mW 16155 = 535888414758079 := by
  have hu : mW 16155 ≤ 535888414758079 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16155 ≤ 535888414758078 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16155 : RowArithmetic 16155 (13378507617083673549/12500000000000000000000) (588052247694045915481773/1000000000000000000000000) (2521505108921373/500000000000000000000000) where
  r0 := (487011881229/1000000000000000000)
  k0 := (3299199227913973/1000000000000000000)
  k6 := (10773260339714293/1000000000000000000)
  q := (179749826147342907521/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16155]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16155]

theorem width_16156 : mW 16156 = 536004524605323 := by
  have hu : mW 16156 ≤ 536004524605323 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16156 ≤ 536004524605322 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16156 : RowArithmetic 16156 (8361415048627476177/7812500000000000000000) (117608734490513305861933/200000000000000000000000) (2521100674032183/500000000000000000000000) where
  r0 := (243483332713/500000000000000000)
  k0 := (3299046070043749/1000000000000000000)
  k6 := (5386463460475931/500000000000000000)
  q := (35951077869794112753/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16156]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16156]

theorem width_16157 : mW 16157 = 536120652420943 := by
  have hu : mW 16157 ≤ 536120652420943 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16157 ≤ 536120652420942 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16157 : RowArithmetic 16157 (1070241647102172161809/1000000000000000000000000) (588035098244387678499821/1000000000000000000000000) (5041392659679451/1000000000000000000000000) where
  r0 := (486921456619/1000000000000000000)
  k0 := (3298892928761807/1000000000000000000)
  k6 := (538629676657209/50000000000000000)
  q := (179760952378429504137/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16157]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16157]

theorem width_16158 : mW 16158 = 536236798206606 := by
  have hu : mW 16158 ≤ 536236798206606 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16158 ≤ 536236798206605 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16158 : RowArithmetic 16158 (1070222171999173431431/1000000000000000000000000) (147006631267327597632609/250000000000000000000000) (5040584152635777/1000000000000000000000000) where
  r0 := (486876254807/1000000000000000000)
  k0 := (329873980406707/100000000000000000)
  k6 := (10772260176286457/1000000000000000000)
  q := (89883257617867856181/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16158]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16158]

theorem width_16159 : mW 16159 = 536352961963982 := by
  have hu : mW 16159 ≤ 536352961963982 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16159 ≤ 536352961963981 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16159 : RowArithmetic 16159 (1070202700914234286747/1000000000000000000000000) (29400897646356778310279/50000000000000000000000) (503977582688111/100000000000000000000000) where
  r0 := (486831059987/1000000000000000000)
  k0 := (659717339190337/200000000000000000)
  k6 := (10771926850373907/1000000000000000000)
  q := (35954415584181033939/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16159]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16159]

theorem width_16160 : mW 16160 = 536469143694739 := by
  have hu : mW 16160 ≤ 536469143694739 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16160 ≤ 536469143694738 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16160 : RowArithmetic 16160 (1070183233846269139193/1000000000000000000000000) (294004690908832177600807/500000000000000000000000) (2519483841181627/500000000000000000000000) where
  r0 := (3042411701/6250000000000000)
  k0 := (824608401105337/250000000000000000)
  k6 := (538579677770087/50000000000000000)
  q := (179777640433953854917/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16160]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16160]

theorem width_16161 : mW 16161 = 536585343400545 := by
  have hu : mW 16161 ≤ 536585343400545 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16161 ≤ 536585343400544 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16161 : RowArithmetic 16161 (1070163770794192775589/1000000000000000000000000) (588000811740697835121289/1000000000000000000000000) (5038159719030033/1000000000000000000000000) where
  r0 := (243370345661/500000000000000000)
  k0 := (659656105892963/200000000000000000)
  k6 := (1077126029136517/100000000000000000)
  q := (179783202774897744339/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16161]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16161]

theorem width_16162 : mW 16162 = 536701561083068 := by
  have hu : mW 16162 ≤ 536701561083068 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16162 ≤ 536701561083067 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16162 : RowArithmetic 16162 (1070144311756920357963/1000000000000000000000000) (587992242696037217641391/1000000000000000000000000) (5037351936829287/1000000000000000000000000) where
  r0 := (243347758737/500000000000000000)
  k0 := (412265933885973/125000000000000000)
  k6 := (10770927058259413/1000000000000000000)
  q := (89894382471876405899/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16162]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16162]

theorem width_16163 : mW 16163 = 536817796743978 := by
  have hu : mW 16163 ≤ 536817796743978 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16163 ≤ 536817796743977 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16163 : RowArithmetic 16163 (535062428366683458001/500000000000000000000000) (293991837341741848437289/500000000000000000000000) (5036544335708857/1000000000000000000000000) where
  r0 := (121662587653/250000000000000000)
  k0 := (3297974429279009/1000000000000000000)
  k6 := (2692648464019921/250000000000000000)
  q := (179794326940535028663/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16163]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16163]

theorem width_16164 : mW 16164 = 536934050384943 := by
  have hu : mW 16164 ≤ 536934050384943 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16164 ≤ 536934050384942 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16164 : RowArithmetic 16164 (267526351430612090551/250000000000000000000000) (293987553851419265857961/500000000000000000000000) (40285895324933/8000000000000000000000) where
  r0 := (30412824421/62500000000000000)
  k0 := (659564280808159/200000000000000000)
  k6 := (10770260684821199/1000000000000000000)
  q := (179799888765260363829/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16164]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16164]

theorem width_16165 : mW 16165 = 537050322007631 := by
  have hu : mW 16165 ≤ 537050322007631 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16165 ≤ 537050322007630 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16165 : RowArithmetic 16165 (1070085958723080983773/1000000000000000000000000) (58796654175390306646071/100000000000000000000000) (5034929676500487/1000000000000000000000000) where
  r0 := (121640009461/250000000000000000)
  k0 := (1648834197684337/500000000000000000)
  k6 := (10769927544479177/1000000000000000000)
  q := (7192218016717791349/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16165]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16165]

theorem width_16166 : mW 16166 = 537166611613711 := by
  have hu : mW 16166 ≤ 537166611613711 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16166 ≤ 537166611613710 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16166 : RowArithmetic 16166 (1070066515734181189037/1000000000000000000000000) (587957976836478702894483/1000000000000000000000000) (100682452366167/20000000000000000000000) where
  r0 := (97302978387/200000000000000000)
  k0 := (3297515403261561/1000000000000000000)
  k6 := (10769594435048837/1000000000000000000)
  q := (44952752974651063077/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16166]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16166]

theorem width_16167 : mW 16167 = 537282919204853 := by
  have hu : mW 16167 ≤ 537282919204853 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16167 ≤ 537282919204852 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16167 : RowArithmetic 16167 (267511769188666376933/250000000000000000000000) (587949412950366847323073/1000000000000000000000000) (5033315740988133/1000000000000000000000000) where
  r0 := (486469753007/1000000000000000000)
  k0 := (412170303464373/125000000000000000)
  k6 := (5384630678262699/500000000000000000)
  q := (44954143301813682767/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16167]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16167]

theorem width_16168 : mW 16168 = 537399244782724 := by
  have hu : mW 16168 ≤ 537399244782724 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16168 ≤ 537399244782723 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16168 : RowArithmetic 16168 (1070027641783451604241/1000000000000000000000000) (587940850095368967838909/1000000000000000000000000) (2516254522243899/500000000000000000000000) where
  r0 := (243212310529/500000000000000000)
  k0 := (329720946872447/100000000000000000)
  k6 := (134611603861301/12500000000000000)
  q := (7192885373756487161/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16168]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16168]

theorem width_16169 : mW 16169 = 537515588348994 := by
  have hu : mW 16169 ≤ 537515588348994 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16169 ≤ 537515588348993 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16169 : RowArithmetic 16169 (535004105409728378591/500000000000000000000000) (587932288271286637048431/1000000000000000000000000) (50317025287553/10000000000000000000000) where
  r0 := (486379496087/1000000000000000000)
  k0 := (1648528263144467/500000000000000000)
  k6 := (10768595292180107/1000000000000000000)
  q := (35965539061718510547/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16169]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16169]

theorem width_16170 : mW 16170 = 537631949905331 := by
  have hu : mW 16170 ≤ 537631949905331 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16170 ≤ 537631949905330 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16170 : RowArithmetic 16170 (534994391930799562943/500000000000000000000000) (5879237274779214894781/10000000000000000000000) (5030896193738631/1000000000000000000000000) where
  r0 := (486334378093/1000000000000000000)
  k0 := (329690360040729/100000000000000000)
  k6 := (10768262306348701/1000000000000000000)
  q := (89916628050655903141/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16170]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16170]

theorem width_16171 : mW 16171 = 537748329453405 := by
  have hu : mW 16171 ≤ 537748329453405 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16171 ≤ 537748329453404 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16171 : RowArithmetic 16171 (66873085056799796091/62500000000000000000000) (58791516771507503602049/100000000000000000000000) (2515045019692891/500000000000000000000000) where
  r0 := (243144633537/500000000000000000)
  k0 := (3296750691075063/1000000000000000000)
  k6 := (5383964675702543/500000000000000000)
  q := (179838816722085891287/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16171]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16171]

theorem width_16172 : mW 16172 = 537864726994885 := by
  have hu : mW 16172 ≤ 537864726994885 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16172 ≤ 537864726994884 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16172 : RowArithmetic 16172 (213989988391993649227/200000000000000000000000) (36744163061409317346107/62500000000000000000000) (201171362625791/40000000000000000000000) where
  r0 := (486244163029/1000000000000000000)
  k0 := (824149449572791/250000000000000000)
  k6 := (1345949553418061/125000000000000000)
  q := (22480547146366344613/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16172]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16172]

theorem width_16173 : mW 16173 = 537981142531439 := by
  have hu : mW 16173 ≤ 537981142531439 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16173 ≤ 537981142531438 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16173 : RowArithmetic 16173 (1069930527014032932683/1000000000000000000000000) (587898051280145335390659/1000000000000000000000000) (628559784057957/125000000000000000000000) where
  r0 := (97239813191/200000000000000000)
  k0 := (206027807627983/62500000000000000)
  k6 := (10767263534162131/1000000000000000000)
  q := (8992496872393117491/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16173]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16173]

theorem width_16174 : mW 16174 = 538097576064737 := by
  have hu : mW 16174 ≤ 538097576064737 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16174 ≤ 538097576064736 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16174 : RowArithmetic 16174 (534955558034954972839/500000000000000000000000) (587889494607665591350519/1000000000000000000000000) (201106906391619/40000000000000000000000) where
  r0 := (121538493963/250000000000000000)
  k0 := (659258412469411/200000000000000000)
  k6 := (10766930671853243/1000000000000000000)
  q := (179855497552896614259/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16174]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16174]

theorem width_16175 : mW 16175 = 538214027596448 := by
  have hu : mW 16175 ≤ 538214027596448 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16175 ≤ 538214027596447 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16175 : RowArithmetic 16175 (1069891709126519060063/1000000000000000000000000) (146970234741227927388631/250000000000000000000000) (5026867227573307/1000000000000000000000000) where
  r0 := (243054446359/500000000000000000)
  k0 := (3296139219184667/1000000000000000000)
  k6 := (5383298920206527/500000000000000000)
  q := (179861057486049491981/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16175]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16175]

theorem width_16176 : mW 16176 = 538330497128241 := by
  have hu : mW 16176 ≤ 538330497128241 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16176 ≤ 538330497128240 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16176 : RowArithmetic 16176 (213974461236556084803/200000000000000000000000) (587872384351685599778879/1000000000000000000000000) (5026061975760247/1000000000000000000000000) where
  r0 := (60757977069/125000000000000000)
  k0 := (205999149534967/62500000000000000)
  k6 := (1076626503983679/100000000000000000)
  q := (179866617247336922279/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16176]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16176]

theorem width_16177 : mW 16177 = 538446984661785 := by
  have hu : mW 16177 ≤ 538446984661785 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16177 ≤ 538446984661784 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16177 : RowArithmetic 16177 (133731613404701819847/125000000000000000000000) (146965957691947307639509/250000000000000000000000) (502525690429941/100000000000000000000000) where
  r0 := (486018747351/1000000000000000000)
  k0 := (3295833582463601/1000000000000000000)
  k6 := (2691483067529921/250000000000000000)
  q := (89936088418387420993/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16177]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16177]

theorem width_16178 : mW 16178 = 538563490198751 := by
  have hu : mW 16178 ≤ 538563490198751 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16178 ≤ 538563490198750 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16178 : RowArithmetic 16178 (106983351228994185383/100000000000000000000000) (36740954888314035762767/62500000000000000000000) (5024452013138909/1000000000000000000000000) where
  r0 := (97194737023/200000000000000000)
  k0 := (411960098612419/125000000000000000)
  k6 := (2153119906251393/200000000000000000)
  q := (179877736254379185469/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16178]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16178]

theorem width_16179 : mW 16179 = 538680013740806 := by
  have hu : mW 16179 ≤ 538680013740806 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16179 ≤ 538680013740805 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16179 : RowArithmetic 16179 (66863382583667755067/62500000000000000000000) (587846726687193765289427/1000000000000000000000000) (5023647302226913/1000000000000000000000000) where
  r0 := (242964314921/500000000000000000)
  k0 := (1647764005931121/500000000000000000)
  k6 := (10765266823243867/1000000000000000000)
  q := (179883295500165884637/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16179]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16179]

theorem width_16180 : mW 16180 = 538796555289621 := by
  have hu : mW 16180 ≤ 538796555289621 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16180 ≤ 538796555289620 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16180 : RowArithmetic 16180 (1069794734382762375649/1000000000000000000000000) (23513527047603953616597/40000000000000000000000) (2511421385755787/500000000000000000000000) where
  r0 := (48588358153/100000000000000000)
  k0 := (3295375251347789/1000000000000000000)
  k6 := (5382467073037811/500000000000000000)
  q := (44972213643537717233/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16180]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16180]

theorem width_16181 : mW 16181 = 538913114846865 := by
  have hu : mW 16181 ≤ 538913114846865 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16181 ≤ 538913114846864 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16181 : RowArithmetic 16181 (133721918927637343743/125000000000000000000000) (2939148133607709778469/5000000000000000000000) (125550960523527/25000000000000000000000) where
  r0 := (485838540179/1000000000000000000)
  k0 := (329522250735829/100000000000000000)
  k6 := (2152920299949493/200000000000000000)
  q := (179894413476350065339/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16181]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16181]

theorem width_16182 : mW 16182 = 539029692414207 := by
  have hu : mW 16182 ≤ 539029692414207 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16182 ≤ 539029692414206 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16182 : RowArithmetic 16182 (33429874139144237143/31250000000000000000000) (29391053914066270846223/50000000000000000000000) (2510617125231819/500000000000000000000000) where
  r0 := (97158701157/200000000000000000)
  k0 := (3295069779882477/1000000000000000000)
  k6 := (1345533610531829/125000000000000000)
  q := (8994998610338969919/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16182]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16182]

theorem width_16183 : mW 16183 = 539146287993318 := by
  have hu : mW 16183 ≤ 539146287993318 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16183 ≤ 539146287993317 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16183 : RowArithmetic 16183 (534868298738117572239/500000000000000000000000) (587812530869251446924983/1000000000000000000000000) (1004086052005491/200000000000000000000000) where
  r0 := (485748478349/1000000000000000000)
  k0 := (1647458534463019/500000000000000000)
  k6 := (5381968149796179/500000000000000000)
  q := (89952765382727395059/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16183]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16183]

theorem width_16184 : mW 16184 = 539262901585866 := by
  have hu : mW 16184 ≤ 539262901585866 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16184 ≤ 539262901585865 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16184 : RowArithmetic 16184 (267429306622720199641/250000000000000000000000) (587803984485122349784011/1000000000000000000000000) (2509813224790393/500000000000000000000000) where
  r0 := (121425864467/250000000000000000)
  k0 := (658952874896219/200000000000000000)
  k6 := (10763603745755881/1000000000000000000)
  q := (35982217830478432031/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16184]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16184]

theorem width_16185 : mW 16185 = 539379533193522 := by
  have hu : mW 16185 ≤ 539379533193522 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16185 ≤ 539379533193521 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16185 : RowArithmetic 16185 (534848929747737774019/500000000000000000000000) (587795439128740513227913/1000000000000000000000000) (2509411409535937/500000000000000000000000) where
  r0 := (485658444341/1000000000000000000)
  k0 := (3294611696546553/1000000000000000000)
  k6 := (269081780568511/25000000000000000)
  q := (35983329473521485127/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16185]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16185]

theorem width_16186 : mW 16186 = 539496182817956 := by
  have hu : mW 16186 ≤ 539496182817956 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16186 ≤ 539496182817955 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16186 : RowArithmetic 16186 (267419624122235753499/250000000000000000000000) (293893447399954204418943/500000000000000000000000) (156813105264031/31250000000000000000000) where
  r0 := (485613437767/1000000000000000000)
  k0 := (3294459035121313/1000000000000000000)
  k6 := (5381469365270637/500000000000000000)
  q := (179922205411116501243/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16186]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16186]

theorem width_16187 : mW 16187 = 539612850460836 := by
  have hu : mW 16187 ≤ 539612850460836 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16187 ≤ 539612850460835 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16187 : RowArithmetic 16187 (534829568735103846167/500000000000000000000000) (29388917574921422465313/50000000000000000000000) (100344321953209/20000000000000000000000) where
  r0 := (485568438143/1000000000000000000)
  k0 := (658861278039499/200000000000000000)
  k6 := (10762606269153623/1000000000000000000)
  q := (179927763282935299207/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16187]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16187]

theorem width_16188 : mW 16188 = 539729536123833 := by
  have hu : mW 16188 ≤ 539729536123833 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16188 ≤ 539729536123832 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16188 : RowArithmetic 16188 (213927956487638739109/200000000000000000000000) (3673561307650645185539/6250000000000000000000) (1254103251663637/250000000000000000000000) where
  r0 := (485523445469/1000000000000000000)
  k0 := (1647076880888697/500000000000000000)
  k6 := (1076227383857273/100000000000000000)
  q := (11245832561442483081/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16188]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16188]

theorem width_16189 : mW 16189 = 539846239808617 := by
  have hu : mW 16189 ≤ 539846239808617 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16189 ≤ 539846239808616 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16189 : RowArithmetic 16189 (267405107847956439813/250000000000000000000000) (73470158497091910571213/125000000000000000000000) (5015610095379613/1000000000000000000000000) where
  r0 := (485478459743/1000000000000000000)
  k0 := (3294001149856517/1000000000000000000)
  k6 := (2690485359698459/250000000000000000)
  q := (89969439255782849411/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16189]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16189]

theorem width_16190 : mW 16190 = 539962961516857 := by
  have hu : mW 16190 ≤ 539962961516857 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16190 ≤ 539962961516856 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16190 : RowArithmetic 16190 (106960108433002924159/100000000000000000000000) (587752727756127254563259/1000000000000000000000000) (1253701840946001/250000000000000000000000) where
  r0 := (485433480963/1000000000000000000)
  k0 := (823462138607593/250000000000000000)
  k6 := (2152321813962437/200000000000000000)
  q := (179944435868409112641/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16190]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16190]

theorem width_16191 : mW 16191 = 540079701250224 := by
  have hu : mW 16191 ≤ 540079701250224 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16191 ≤ 540079701250223 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16191 : RowArithmetic 16191 (534790870625864684561/500000000000000000000000) (587744188562081840352137/1000000000000000000000000) (200560192472643/40000000000000000000000) where
  r0 := (60673563641/125000000000000000)
  k0 := (3293695975497861/1000000000000000000)
  k6 := (5380638365811511/500000000000000000)
  q := (89974996526812936577/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16191]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16191]

theorem width_16192 : mW 16192 = 540196459010389 := by
  have hu : mW 16192 ≤ 540196459010389 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16192 ≤ 540196459010388 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16192 : RowArithmetic 16192 (1069562402155851739711/1000000000000000000000000) (587735650394401851517991/1000000000000000000000000) (5013202439424201/1000000000000000000000000) where
  r0 := (485343544237/1000000000000000000)
  k0 := (3293543413057881/1000000000000000000)
  k6 := (10760944424221593/1000000000000000000)
  q := (35991110013446376061/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16192]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16192]

theorem width_16193 : mW 16193 = 540313234799019 := by
  have hu : mW 16193 ≤ 540313234799019 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16193 ≤ 540313234799018 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16193 : RowArithmetic 16193 (1069543067041323326243/1000000000000000000000000) (587727113252889943004523/1000000000000000000000000) (5012400246556813/1000000000000000000000000) where
  r0 := (485298586287/1000000000000000000)
  k0 := (658678173420509/200000000000000000)
  k6 := (10760612147603143/1000000000000000000)
  q := (5623784590913844737/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16193]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16193]

theorem width_16194 : mW 16194 = 540430028617787 := by
  have hu : mW 16194 ≤ 540430028617787 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16194 ≤ 540430028617786 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16194 : RowArithmetic 16194 (2088913546693496027/1953125000000000000000) (293859288568674514325203/500000000000000000000000) (1002319646632461/200000000000000000000000) where
  r0 := (242626817639/500000000000000000)
  k0 := (102913698051067/31250000000000000)
  k6 := (5380139950881461/500000000000000000)
  q := (44991665894918805507/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16194]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16194]

theorem width_16195 : mW 16195 = 540546840468362 := by
  have hu : mW 16195 ≤ 540546840468362 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16195 ≤ 540546840468361 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16195 : RowArithmetic 16195 (66844025547001179391/62500000000000000000000) (587710042047582061797359/1000000000000000000000000) (40086371193513/8000000000000000000000) where
  r0 := (60651086401/125000000000000000)
  k0 := (3293085824648183/1000000000000000000)
  k6 := (10759947686696177/1000000000000000000)
  q := (22496527509818043027/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16195]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16195]

theorem width_16196 : mW 16196 = 540663670352415 := by
  have hu : mW 16196 ≤ 540663670352415 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16196 ≤ 540663670352414 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16196 : RowArithmetic 16196 (1069485085575097119843/1000000000000000000000000) (587701507983391888471619/1000000000000000000000000) (2504997372292861/500000000000000000000000) where
  r0 := (19406550163/40000000000000000)
  k0 := (3292933328140163/1000000000000000000)
  k6 := (10759615502398159/1000000000000000000)
  q := (89988888202933144139/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16196]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16196]

theorem width_16197 : mW 16197 = 540780518271615 := by
  have hu : mW 16197 ≤ 540780518271615 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16197 ≤ 540780518271614 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16197 : RowArithmetic 16197 (1069465766375232666589/1000000000000000000000000) (117538594988916317371701/200000000000000000000000) (5009193269300583/1000000000000000000000000) where
  r0 := (242559411939/500000000000000000)
  k0 := (3292780848108981/1000000000000000000)
  k6 := (5379641674432059/500000000000000000)
  q := (17998333256165694189/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16197]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16197]

theorem width_16198 : mW 16198 = 540897384227634 := by
  have hu : mW 16198 ≤ 540897384227634 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16198 ≤ 540897384227633 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16198 : RowArithmetic 16198 (534723225575676540253/500000000000000000000000) (587684442930954192432211/1000000000000000000000000) (1001678394656437/200000000000000000000000) where
  r0 := (60634237577/125000000000000000)
  k0 := (823157096138383/250000000000000000)
  k6 := (5379475613044653/500000000000000000)
  q := (7199555541837287611/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16198]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16198]

theorem width_16199 : mW 16199 = 541014268222141 := by
  have hu : mW 16199 ≤ 541014268222141 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16199 ≤ 541014268222140 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16199 : RowArithmetic 16199 (1069427139902387053407/1000000000000000000000000) (293837955971156381283237/500000000000000000000000) (5007590856479051/1000000000000000000000000) where
  r0 := (242514492143/500000000000000000)
  k0 := (1646237968732961/500000000000000000)
  k6 := (430344765362759/40000000000000000)
  q := (35998888871741583241/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16199]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16199]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 16130 then ⟨(535384498843397773129/500000000000000000000000), (588266965136986741471591/1000000000000000000000000), (5063291068348033/1000000000000000000000000)⟩ else
  if n = 16131 then ⟨(267687353421116030309/250000000000000000000000), (73532295499768833904971/125000000000000000000000), (2531238823351103/500000000000000000000000)⟩ else
  if n = 16132 then ⟨(1070729833729643883147/1000000000000000000000000), (588249763897608358499781/1000000000000000000000000), (5061664407761761/1000000000000000000000000)⟩ else
  if n = 16133 then ⟨(1070710257821239046333/1000000000000000000000000), (294120582417579724896811/500000000000000000000000), (632606418934249/125000000000000000000000)⟩ else
  if n = 16134 then ⟨(1070690685958154205081/1000000000000000000000000), (7352907085132545359139/12500000000000000000000), (158126202430819/31250000000000000000000)⟩ else
  if n = 16135 then ⟨(1070671118139295102243/1000000000000000000000000), (147055992455935152935097/250000000000000000000000), (5059225786645769/1000000000000000000000000)⟩ else
  if n = 16136 then ⟨(214130310872713366897/200000000000000000000000), (588215373874370213851433/1000000000000000000000000), (316150829875001/62500000000000000000000)⟩ else
  if n = 16137 then ⟨(267657998657468847609/250000000000000000000000), (588206778962292322663911/1000000000000000000000000), (202304038071853/40000000000000000000000)⟩ else
  if n = 16138 then ⟨(1070612438937127137619/1000000000000000000000000), (294099092543653384233103/500000000000000000000000), (316049300498881/62500000000000000000000)⟩ else
  if n = 16139 then ⟨(535296443642114411143/500000000000000000000000), (588189592249213527646427/1000000000000000000000000), (2527988423252371/500000000000000000000000)⟩ else
  if n = 16140 then ⟨(535286669835043656721/500000000000000000000000), (588181000447812620693787/1000000000000000000000000), (5055165067311691/1000000000000000000000000)⟩ else
  if n = 16141 then ⟨(1070553796093610370269/1000000000000000000000000), (117634481936580821674871/200000000000000000000000), (1010870694070081/200000000000000000000000)⟩ else
  if n = 16142 then ⟨(214106851310741072589/200000000000000000000000), (147040954988572027945713/250000000000000000000000), (2526771027784169/500000000000000000000000)⟩ else
  if n = 16143 then ⟨(267628680262320137871/250000000000000000000000), (58815523126176475668557/100000000000000000000000), (631591352864123/125000000000000000000000)⟩ else
  if n = 16144 then ⟨(214099037915848863669/200000000000000000000000), (294073321802567156680277/500000000000000000000000), (2525959886165921/500000000000000000000000)⟩ else
  if n = 16145 then ⟨(1070475662142505679409/1000000000000000000000000), (588138056984197053561131/1000000000000000000000000), (1262777225943111/250000000000000000000000)⟩ else
  if n = 16146 then ⟨(214091227747594805619/200000000000000000000000), (36758091962422077909603/62500000000000000000000), (2525149108591169/500000000000000000000000)⟩ else
  if n = 16147 then ⟨(13380457742056982811/12500000000000000000000), (147030221712150828291321/250000000000000000000000), (5049487712509073/1000000000000000000000000)⟩ else
  if n = 16148 then ⟨(267604276005292340811/250000000000000000000000), (294056151666773846031247/500000000000000000000000), (2524338694850113/500000000000000000000000)⟩ else
  if n = 16149 then ⟨(1070397592706716769043/1000000000000000000000000), (147025930213346715852819/250000000000000000000000), (5047867248703403/1000000000000000000000000)⟩ else
  if n = 16150 then ⟨(214075617084022298023/200000000000000000000000), (147023784851980327594253/250000000000000000000000), (252352864473311/50000000000000000000000)⟩ else
  if n = 16151 then ⟨(535179291080132275681/500000000000000000000000), (294043279498475850142143/500000000000000000000000), (504624751193631/100000000000000000000000)⟩ else
  if n = 16152 then ⟨(535169541463043677291/500000000000000000000000), (294038989810139311286873/500000000000000000000000), (2522718958030663/500000000000000000000000)⟩ else
  if n = 16153 then ⟨(133789948464561459787/125000000000000000000000), (294034700638851406276473/500000000000000000000000), (252231425089447/50000000000000000000000)⟩ else
  if n = 16154 then ⟨(535150048265194838793/500000000000000000000000), (294030411984512477088309/500000000000000000000000), (1260954817266711/250000000000000000000000)⟩ else
  if n = 16155 then ⟨(13378507617083673549/12500000000000000000000), (588052247694045915481773/1000000000000000000000000), (2521505108921373/500000000000000000000000)⟩ else
  if n = 16156 then ⟨(8361415048627476177/7812500000000000000000), (117608734490513305861933/200000000000000000000000), (2521100674032183/500000000000000000000000)⟩ else
  if n = 16157 then ⟨(1070241647102172161809/1000000000000000000000000), (588035098244387678499821/1000000000000000000000000), (5041392659679451/1000000000000000000000000)⟩ else
  if n = 16158 then ⟨(1070222171999173431431/1000000000000000000000000), (147006631267327597632609/250000000000000000000000), (5040584152635777/1000000000000000000000000)⟩ else
  if n = 16159 then ⟨(1070202700914234286747/1000000000000000000000000), (29400897646356778310279/50000000000000000000000), (503977582688111/100000000000000000000000)⟩ else
  if n = 16160 then ⟨(1070183233846269139193/1000000000000000000000000), (294004690908832177600807/500000000000000000000000), (2519483841181627/500000000000000000000000)⟩ else
  if n = 16161 then ⟨(1070163770794192775589/1000000000000000000000000), (588000811740697835121289/1000000000000000000000000), (5038159719030033/1000000000000000000000000)⟩ else
  if n = 16162 then ⟨(1070144311756920357963/1000000000000000000000000), (587992242696037217641391/1000000000000000000000000), (5037351936829287/1000000000000000000000000)⟩ else
  if n = 16163 then ⟨(535062428366683458001/500000000000000000000000), (293991837341741848437289/500000000000000000000000), (5036544335708857/1000000000000000000000000)⟩ else
  if n = 16164 then ⟨(267526351430612090551/250000000000000000000000), (293987553851419265857961/500000000000000000000000), (40285895324933/8000000000000000000000)⟩ else
  if n = 16165 then ⟨(1070085958723080983773/1000000000000000000000000), (58796654175390306646071/100000000000000000000000), (5034929676500487/1000000000000000000000000)⟩ else
  if n = 16166 then ⟨(1070066515734181189037/1000000000000000000000000), (587957976836478702894483/1000000000000000000000000), (100682452366167/20000000000000000000000)⟩ else
  if n = 16167 then ⟨(267511769188666376933/250000000000000000000000), (587949412950366847323073/1000000000000000000000000), (5033315740988133/1000000000000000000000000)⟩ else
  if n = 16168 then ⟨(1070027641783451604241/1000000000000000000000000), (587940850095368967838909/1000000000000000000000000), (2516254522243899/500000000000000000000000)⟩ else
  if n = 16169 then ⟨(535004105409728378591/500000000000000000000000), (587932288271286637048431/1000000000000000000000000), (50317025287553/10000000000000000000000)⟩ else
  if n = 16170 then ⟨(534994391930799562943/500000000000000000000000), (5879237274779214894781/10000000000000000000000), (5030896193738631/1000000000000000000000000)⟩ else
  if n = 16171 then ⟨(66873085056799796091/62500000000000000000000), (58791516771507503602049/100000000000000000000000), (2515045019692891/500000000000000000000000)⟩ else
  if n = 16172 then ⟨(213989988391993649227/200000000000000000000000), (36744163061409317346107/62500000000000000000000), (201171362625791/40000000000000000000000)⟩ else
  if n = 16173 then ⟨(1069930527014032932683/1000000000000000000000000), (587898051280145335390659/1000000000000000000000000), (628559784057957/125000000000000000000000)⟩ else
  if n = 16174 then ⟨(534955558034954972839/500000000000000000000000), (587889494607665591350519/1000000000000000000000000), (201106906391619/40000000000000000000000)⟩ else
  if n = 16175 then ⟨(1069891709126519060063/1000000000000000000000000), (146970234741227927388631/250000000000000000000000), (5026867227573307/1000000000000000000000000)⟩ else
  if n = 16176 then ⟨(213974461236556084803/200000000000000000000000), (587872384351685599778879/1000000000000000000000000), (5026061975760247/1000000000000000000000000)⟩ else
  if n = 16177 then ⟨(133731613404701819847/125000000000000000000000), (146965957691947307639509/250000000000000000000000), (502525690429941/100000000000000000000000)⟩ else
  if n = 16178 then ⟨(106983351228994185383/100000000000000000000000), (36740954888314035762767/62500000000000000000000), (5024452013138909/1000000000000000000000000)⟩ else
  if n = 16179 then ⟨(66863382583667755067/62500000000000000000000), (587846726687193765289427/1000000000000000000000000), (5023647302226913/1000000000000000000000000)⟩ else
  if n = 16180 then ⟨(1069794734382762375649/1000000000000000000000000), (23513527047603953616597/40000000000000000000000), (2511421385755787/500000000000000000000000)⟩ else
  if n = 16181 then ⟨(133721918927637343743/125000000000000000000000), (2939148133607709778469/5000000000000000000000), (125550960523527/25000000000000000000000)⟩ else
  if n = 16182 then ⟨(33429874139144237143/31250000000000000000000), (29391053914066270846223/50000000000000000000000), (2510617125231819/500000000000000000000000)⟩ else
  if n = 16183 then ⟨(534868298738117572239/500000000000000000000000), (587812530869251446924983/1000000000000000000000000), (1004086052005491/200000000000000000000000)⟩ else
  if n = 16184 then ⟨(267429306622720199641/250000000000000000000000), (587803984485122349784011/1000000000000000000000000), (2509813224790393/500000000000000000000000)⟩ else
  if n = 16185 then ⟨(534848929747737774019/500000000000000000000000), (587795439128740513227913/1000000000000000000000000), (2509411409535937/500000000000000000000000)⟩ else
  if n = 16186 then ⟨(267419624122235753499/250000000000000000000000), (293893447399954204418943/500000000000000000000000), (156813105264031/31250000000000000000000)⟩ else
  if n = 16187 then ⟨(534829568735103846167/500000000000000000000000), (29388917574921422465313/50000000000000000000000), (100344321953209/20000000000000000000000)⟩ else
  if n = 16188 then ⟨(213927956487638739109/200000000000000000000000), (3673561307650645185539/6250000000000000000000), (1254103251663637/250000000000000000000000)⟩ else
  if n = 16189 then ⟨(267405107847956439813/250000000000000000000000), (73470158497091910571213/125000000000000000000000), (5015610095379613/1000000000000000000000000)⟩ else
  if n = 16190 then ⟨(106960108433002924159/100000000000000000000000), (587752727756127254563259/1000000000000000000000000), (1253701840946001/250000000000000000000000)⟩ else
  if n = 16191 then ⟨(534790870625864684561/500000000000000000000000), (587744188562081840352137/1000000000000000000000000), (200560192472643/40000000000000000000000)⟩ else
  if n = 16192 then ⟨(1069562402155851739711/1000000000000000000000000), (587735650394401851517991/1000000000000000000000000), (5013202439424201/1000000000000000000000000)⟩ else
  if n = 16193 then ⟨(1069543067041323326243/1000000000000000000000000), (587727113252889943004523/1000000000000000000000000), (5012400246556813/1000000000000000000000000)⟩ else
  if n = 16194 then ⟨(2088913546693496027/1953125000000000000000), (293859288568674514325203/500000000000000000000000), (1002319646632461/200000000000000000000000)⟩ else
  if n = 16195 then ⟨(66844025547001179391/62500000000000000000000), (587710042047582061797359/1000000000000000000000000), (40086371193513/8000000000000000000000)⟩ else
  if n = 16196 then ⟨(1069485085575097119843/1000000000000000000000000), (587701507983391888471619/1000000000000000000000000), (2504997372292861/500000000000000000000000)⟩ else
  if n = 16197 then ⟨(1069465766375232666589/1000000000000000000000000), (117538594988916317371701/200000000000000000000000), (5009193269300583/1000000000000000000000000)⟩ else
  if n = 16198 then ⟨(534723225575676540253/500000000000000000000000), (587684442930954192432211/1000000000000000000000000), (1001678394656437/200000000000000000000000)⟩ else
  ⟨(1069427139902387053407/1000000000000000000000000), (293837955971156381283237/500000000000000000000000), (5007590856479051/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 16130 ≤ n) (hb : n ≤ 16199) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_16130
  · exact row_16131
  · exact row_16132
  · exact row_16133
  · exact row_16134
  · exact row_16135
  · exact row_16136
  · exact row_16137
  · exact row_16138
  · exact row_16139
  · exact row_16140
  · exact row_16141
  · exact row_16142
  · exact row_16143
  · exact row_16144
  · exact row_16145
  · exact row_16146
  · exact row_16147
  · exact row_16148
  · exact row_16149
  · exact row_16150
  · exact row_16151
  · exact row_16152
  · exact row_16153
  · exact row_16154
  · exact row_16155
  · exact row_16156
  · exact row_16157
  · exact row_16158
  · exact row_16159
  · exact row_16160
  · exact row_16161
  · exact row_16162
  · exact row_16163
  · exact row_16164
  · exact row_16165
  · exact row_16166
  · exact row_16167
  · exact row_16168
  · exact row_16169
  · exact row_16170
  · exact row_16171
  · exact row_16172
  · exact row_16173
  · exact row_16174
  · exact row_16175
  · exact row_16176
  · exact row_16177
  · exact row_16178
  · exact row_16179
  · exact row_16180
  · exact row_16181
  · exact row_16182
  · exact row_16183
  · exact row_16184
  · exact row_16185
  · exact row_16186
  · exact row_16187
  · exact row_16188
  · exact row_16189
  · exact row_16190
  · exact row_16191
  · exact row_16192
  · exact row_16193
  · exact row_16194
  · exact row_16195
  · exact row_16196
  · exact row_16197
  · exact row_16198
  · exact row_16199

end BstLean.Part271.R3.Rows16130
