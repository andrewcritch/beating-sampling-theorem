import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15602–15624. -/
namespace BstLean.Part271.R3.Rows15602
open Real BstLean.Part130 BstLean.Part227

theorem width_15602 : mW 15602 = 474385010101433 := by
  have hu : mW 15602 ≤ 474385010101433 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15602 ≤ 474385010101432 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15602 : RowArithmetic 15602 (43268115698131308783/40000000000000000000000) (592958494414084952356769/1000000000000000000000000) (2759828690048677/500000000000000000000000) where
  r0 := (513132579691/1000000000000000000)
  k0 := (1693259663791547/500000000000000000)
  k6 := (10962522538055963/1000000000000000000)
  q := (176646539734012338791/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15602]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15602]

theorem width_15603 : mW 15603 = 474491437518638 := by
  have hu : mW 15603 ≤ 474491437518638 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15603 ≤ 474491437518637 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15603 : RowArithmetic 15603 (1081681008827349232623/1000000000000000000000000) (592949315701703696338123/1000000000000000000000000) (2759369822981641/500000000000000000000000) where
  r0 := (513083250297/1000000000000000000)
  k0 := (846589136038623/250000000000000000)
  k6 := (10962171237082069/1000000000000000000)
  q := (5520381270800052267/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15603]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15603]

theorem width_15604 : mW 15604 = 474597881989606 := by
  have hu : mW 15604 ≤ 474597881989606 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15604 ≤ 474597881989605 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15604 : RowArithmetic 15604 (1081659129882357738887/1000000000000000000000000) (592940138141296590437231/1000000000000000000000000) (1379455531288453/250000000000000000000000) where
  r0 := (256516964403/500000000000000000)
  k0 := (3386193778981661/1000000000000000000)
  k6 := (2740454992469749/250000000000000000)
  q := (35331572283157736653/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15604]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15604]

theorem width_15605 : mW 15605 = 474704343515976 := by
  have hu : mW 15605 ≤ 474704343515976 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15605 ≤ 474704343515975 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15605 : RowArithmetic 15605 (1081637255616997292519/1000000000000000000000000) (592930961732632445655853/1000000000000000000000000) (5516904817605281/1000000000000000000000000) where
  r0 := (512984615217/1000000000000000000)
  k0 := (1693015516031967/500000000000000000)
  k6 := (2192293747288267/200000000000000000)
  q := (35332704396918161747/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15605]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15605]

theorem width_15606 : mW 15606 = 474810822099387 := by
  have hu : mW 15606 ≤ 474810822099387 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15606 ≤ 474810822099386 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15606 : RowArithmetic 15606 (135201923253744677181/125000000000000000000000) (592921786475480231799009/1000000000000000000000000) (2757993861627023/500000000000000000000000) where
  r0 := (512935309527/1000000000000000000)
  k0 := (3385868303394043/1000000000000000000)
  k6 := (438444701470547/40000000000000000)
  q := (8833459118601274197/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15606]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15606]

theorem width_15607 : mW 15607 = 474917317741480 := by
  have hu : mW 15607 ≤ 474917317741480 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15607 ≤ 474917317741479 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15607 : RowArithmetic 15607 (1081593521119927485241/1000000000000000000000000) (148228153092402256067441/250000000000000000000000) (2757535421018233/500000000000000000000000) where
  r0 := (102577202347/200000000000000000)
  k0 := (846426398242829/250000000000000000)
  k6 := (10960766370840611/1000000000000000000)
  q := (7066993703124405643/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15607]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15607]

theorem width_15608 : mW 15608 = 475023830443894 := by
  have hu : mW 15608 ≤ 475023830443894 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15608 ≤ 475023830443893 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15608 : RowArithmetic 15608 (54078583044279897971/50000000000000000000000) (296451719707393930688181/500000000000000000000000) (1378538543472237/250000000000000000000000) where
  r0 := (512836721839/1000000000000000000)
  k0 := (677108580158357/200000000000000000)
  k6 := (5480207619333367/500000000000000000)
  q := (8834025130143110477/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15608]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15608]

theorem width_15609 : mW 15609 = 475130360208269 := by
  have hu : mW 15609 ≤ 475130360208269 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15609 ≤ 475130360208268 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15609 : RowArithmetic 15609 (1081549805325659461903/1000000000000000000000000) (59289426761078582956717/100000000000000000000000) (5513237718747909/1000000000000000000000000) where
  r0 := (512787439837/1000000000000000000)
  k0 := (846345056712869/250000000000000000)
  k6 := (10960064140236639/1000000000000000000)
  q := (88343081223149557973/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15609]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15609]

theorem width_15610 : mW 15610 = 475236907036244 := by
  have hu : mW 15610 ≤ 475236907036244 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15610 ≤ 475236907036243 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15610 : RowArithmetic 15610 (270381988609700848647/250000000000000000000000) (592885096957372212362141/1000000000000000000000000) (2756160738274901/500000000000000000000000) where
  r0 := (16023067679/31250000000000000)
  k0 := (3385217571149719/1000000000000000000)
  k6 := (10959713075544923/1000000000000000000)
  q := (176691822108438284111/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15610]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15610]

theorem width_15611 : mW 15611 = 475343470929460 := by
  have hu : mW 15611 ≤ 475343470929460 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15611 ≤ 475343470929459 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15611 : RowArithmetic 15611 (1081506108223721007069/1000000000000000000000000) (592875927454316253056291/1000000000000000000000000) (5511405447231083/1000000000000000000000000) where
  r0 := (51268889951/100000000000000000)
  k0 := (169252746684127/50000000000000000)
  k6 := (10959362044586181/1000000000000000000)
  q := (35339496317859427013/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15611]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15611]

theorem width_15612 : mW 15612 = 475450051889555 := by
  have hu : mW 15612 ≤ 475450051889555 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15612 ≤ 475450051889554 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15612 : RowArithmetic 15612 (540742133339552474739/500000000000000000000000) (592866759101387262312439/1000000000000000000000000) (5510489630728263/1000000000000000000000000) where
  r0 := (512639641181/1000000000000000000)
  k0 := (846223078611491/250000000000000000)
  k6 := (2739752761838753/250000000000000000)
  q := (44175785222223271761/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15612]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15612]

theorem width_15613 : mW 15613 = 475556649918171 := by
  have hu : mW 15613 ≤ 475556649918171 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15613 ≤ 475556649918170 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15613 : RowArithmetic 15613 (540731214901823549341/500000000000000000000000) (296428795949177322347331/500000000000000000000000) (688696753372229/125000000000000000000000) where
  r0 := (512590390739/1000000000000000000)
  k0 := (211545607089751/62500000000000000)
  k6 := (85614531905047/7812500000000000)
  q := (353417600014487111/2000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15613]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15613]

theorem width_15614 : mW 15614 = 475663265016947 := by
  have hu : mW 15614 ≤ 475663265016947 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15614 ≤ 475663265016946 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15614 : RowArithmetic 15614 (135180074699505091427/125000000000000000000000) (296424212922493944863423/500000000000000000000000) (275432931795817/50000000000000000000000) where
  r0 := (512541148183/1000000000000000000)
  k0 := (3384567130652021/1000000000000000000)
  k6 := (10958309154053793/1000000000000000000)
  q := (176714458944365953091/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15614]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15614]

theorem width_15615 : mW 15615 = 475769897187522 := by
  have hu : mW 15615 ≤ 475769897187522 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15615 ≤ 475769897187521 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15615 : RowArithmetic 15615 (1081418770054979592237/1000000000000000000000000) (148209815235264122740943/250000000000000000000000) (5507743457480357/1000000000000000000000000) where
  r0 := (51249191351/100000000000000000)
  k0 := (33844045660867/10000000000000000)
  k6 := (684872391123309/62500000000000000)
  q := (44180029425069422423/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15615]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15615]

theorem width_15616 : mW 15616 = 475876546431538 := by
  have hu : mW 15616 ≤ 475876546431538 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15616 ≤ 475876546431537 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15616 : RowArithmetic 15616 (1081396947179156963553/1000000000000000000000000) (59283009718633003871333/100000000000000000000000) (2753414245803223/500000000000000000000000) where
  r0 := (400345849/781250000000000)
  k0 := (1692121009871339/500000000000000000)
  k6 := (10957607395598073/1000000000000000000)
  q := (44181444068749043097/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15616]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15616]

theorem width_15617 : mW 15617 = 475983212750634 := by
  have hu : mW 15617 ≤ 475983212750634 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15617 ≤ 475983212750633 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15617 : RowArithmetic 15617 (1081375128967267525951/1000000000000000000000000) (592820934580578181793881/1000000000000000000000000) (220236549529249/40000000000000000000000) where
  r0 := (512393467809/1000000000000000000)
  k0 := (3384079491609373/1000000000000000000)
  k6 := (1369657070865473/125000000000000000)
  q := (176731434668538805477/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15617]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15617]

theorem width_15618 : mW 15618 = 476089896146451 := by
  have hu : mW 15618 ≤ 476089896146451 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15618 ≤ 476089896146450 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15618 : RowArithmetic 15618 (216270663083601161563/200000000000000000000000) (592811773123570621540651/1000000000000000000000000) (1100999839458263/200000000000000000000000) where
  r0 := (512344256777/1000000000000000000)
  k0 := (52873702838897/15625000000000000)
  k6 := (5478452885972341/500000000000000000)
  q := (176737092880922990473/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15618]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15618]

theorem width_15619 : mW 15619 = 476196596620628 := by
  have hu : mW 15619 ≤ 476196596620628 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15619 ≤ 476196596620627 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15619 : RowArithmetic 15619 (1081331506530067424549/1000000000000000000000000) (592802612815077148732213/1000000000000000000000000) (5504084868723383/1000000000000000000000000) where
  r0 := (256147526811/500000000000000000)
  k0 := (1691877244989401/500000000000000000)
  k6 := (87652440085243/8000000000000000)
  q := (88371375456083063051/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15619]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15619]

theorem width_15620 : mW 15620 = 476303314174807 := by
  have hu : mW 15620 ≤ 476303314174807 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15620 ≤ 476303314174806 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15620 : RowArithmetic 15620 (540654851151073764963/500000000000000000000000) (592793453654867621425851/1000000000000000000000000) (1100634150492817/200000000000000000000000) where
  r0 := (512245858341/1000000000000000000)
  k0 := (3383592016470271/1000000000000000000)
  k6 := (2739051070762617/250000000000000000)
  q := (176748408762285608307/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15620]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15620]

theorem width_15621 : mW 15621 = 476410048810626 := by
  have hu : mW 15621 ≤ 476410048810626 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15621 ≤ 476410048810625 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15621 : RowArithmetic 15621 (270321975683235745747/250000000000000000000000) (37049018477669495139933/62500000000000000000000) (2751128424225073/500000000000000000000000) where
  r0 := (256098335467/500000000000000000)
  k0 := (845857390291609/250000000000000000)
  k6 := (10955853589124573/1000000000000000000)
  q := (88377033215649415123/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15621]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15621]

theorem width_15622 : mW 15622 = 476516800529727 := by
  have hu : mW 15622 ≤ 476516800529727 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15622 ≤ 476516800529726 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15622 : RowArithmetic 15622 (27031652695528746793/25000000000000000000000) (592775138778380005482143/1000000000000000000000000) (550134315661827/100000000000000000000000) where
  r0 := (256073745699/500000000000000000)
  k0 := (845816781015003/250000000000000000)
  k6 := (10955502928872299/1000000000000000000)
  q := (35351944783844636459/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15622]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15622]

theorem width_15623 : mW 15623 = 476623569333751 := by
  have hu : mW 15623 ≤ 476623569333751 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15623 ≤ 476623569333750 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15623 : RowArithmetic 15623 (1081244317565465060687/1000000000000000000000000) (148191495765410487169499/250000000000000000000000) (1100085935381039/200000000000000000000000) where
  r0 := (512098319731/1000000000000000000)
  k0 := (845776176286753/250000000000000000)
  k6 := (10955152302288257/1000000000000000000)
  q := (44191345306519013011/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15623]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15623]

theorem width_15624 : mW 15624 = 476730355224336 := by
  have hu : mW 15624 ≤ 476730355224336 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15624 ≤ 476730355224335 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15624 : RowArithmetic 15624 (540611265982293404119/500000000000000000000000) (118551365698453560476299/200000000000000000000000) (5499516409247717/1000000000000000000000000) where
  r0 := (512049155933/1000000000000000000)
  k0 := (1691471152215029/500000000000000000)
  k6 := (547740085468353/50000000000000000)
  q := (176771038351874824303/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15624]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15624]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 15602 then ⟨(43268115698131308783/40000000000000000000000), (592958494414084952356769/1000000000000000000000000), (2759828690048677/500000000000000000000000)⟩ else
  if n = 15603 then ⟨(1081681008827349232623/1000000000000000000000000), (592949315701703696338123/1000000000000000000000000), (2759369822981641/500000000000000000000000)⟩ else
  if n = 15604 then ⟨(1081659129882357738887/1000000000000000000000000), (592940138141296590437231/1000000000000000000000000), (1379455531288453/250000000000000000000000)⟩ else
  if n = 15605 then ⟨(1081637255616997292519/1000000000000000000000000), (592930961732632445655853/1000000000000000000000000), (5516904817605281/1000000000000000000000000)⟩ else
  if n = 15606 then ⟨(135201923253744677181/125000000000000000000000), (592921786475480231799009/1000000000000000000000000), (2757993861627023/500000000000000000000000)⟩ else
  if n = 15607 then ⟨(1081593521119927485241/1000000000000000000000000), (148228153092402256067441/250000000000000000000000), (2757535421018233/500000000000000000000000)⟩ else
  if n = 15608 then ⟨(54078583044279897971/50000000000000000000000), (296451719707393930688181/500000000000000000000000), (1378538543472237/250000000000000000000000)⟩ else
  if n = 15609 then ⟨(1081549805325659461903/1000000000000000000000000), (59289426761078582956717/100000000000000000000000), (5513237718747909/1000000000000000000000000)⟩ else
  if n = 15610 then ⟨(270381988609700848647/250000000000000000000000), (592885096957372212362141/1000000000000000000000000), (2756160738274901/500000000000000000000000)⟩ else
  if n = 15611 then ⟨(1081506108223721007069/1000000000000000000000000), (592875927454316253056291/1000000000000000000000000), (5511405447231083/1000000000000000000000000)⟩ else
  if n = 15612 then ⟨(540742133339552474739/500000000000000000000000), (592866759101387262312439/1000000000000000000000000), (5510489630728263/1000000000000000000000000)⟩ else
  if n = 15613 then ⟨(540731214901823549341/500000000000000000000000), (296428795949177322347331/500000000000000000000000), (688696753372229/125000000000000000000000)⟩ else
  if n = 15614 then ⟨(135180074699505091427/125000000000000000000000), (296424212922493944863423/500000000000000000000000), (275432931795817/50000000000000000000000)⟩ else
  if n = 15615 then ⟨(1081418770054979592237/1000000000000000000000000), (148209815235264122740943/250000000000000000000000), (5507743457480357/1000000000000000000000000)⟩ else
  if n = 15616 then ⟨(1081396947179156963553/1000000000000000000000000), (59283009718633003871333/100000000000000000000000), (2753414245803223/500000000000000000000000)⟩ else
  if n = 15617 then ⟨(1081375128967267525951/1000000000000000000000000), (592820934580578181793881/1000000000000000000000000), (220236549529249/40000000000000000000000)⟩ else
  if n = 15618 then ⟨(216270663083601161563/200000000000000000000000), (592811773123570621540651/1000000000000000000000000), (1100999839458263/200000000000000000000000)⟩ else
  if n = 15619 then ⟨(1081331506530067424549/1000000000000000000000000), (592802612815077148732213/1000000000000000000000000), (5504084868723383/1000000000000000000000000)⟩ else
  if n = 15620 then ⟨(540654851151073764963/500000000000000000000000), (592793453654867621425851/1000000000000000000000000), (1100634150492817/200000000000000000000000)⟩ else
  if n = 15621 then ⟨(270321975683235745747/250000000000000000000000), (37049018477669495139933/62500000000000000000000), (2751128424225073/500000000000000000000000)⟩ else
  if n = 15622 then ⟨(27031652695528746793/25000000000000000000000), (592775138778380005482143/1000000000000000000000000), (550134315661827/100000000000000000000000)⟩ else
  if n = 15623 then ⟨(1081244317565465060687/1000000000000000000000000), (148191495765410487169499/250000000000000000000000), (1100085935381039/200000000000000000000000)⟩ else
  ⟨(540611265982293404119/500000000000000000000000), (118551365698453560476299/200000000000000000000000), (5499516409247717/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15602 ≤ n) (hb : n ≤ 15624) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15602
  · exact row_15603
  · exact row_15604
  · exact row_15605
  · exact row_15606
  · exact row_15607
  · exact row_15608
  · exact row_15609
  · exact row_15610
  · exact row_15611
  · exact row_15612
  · exact row_15613
  · exact row_15614
  · exact row_15615
  · exact row_15616
  · exact row_15617
  · exact row_15618
  · exact row_15619
  · exact row_15620
  · exact row_15621
  · exact row_15622
  · exact row_15623
  · exact row_15624

end BstLean.Part271.R3.Rows15602
