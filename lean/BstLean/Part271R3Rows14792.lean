import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14792–14866. -/
namespace BstLean.Part271.R3.Rows14792
open Real BstLean.Part130 BstLean.Part227

theorem width_14792 : mW 14792 = 393635395924928 := by
  have hu : mW 14792 ≤ 393635395924928 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14792 ≤ 393635395924927 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14792 : RowArithmetic 14792 (110109145258355469167/100000000000000000000000) (938739671825635298183/1562500000000000000000) (1584800175256151/250000000000000000000000) where
  r0 := (27792630727/50000000000000000)
  k0 := (3524671039255863/1000000000000000000)
  k6 := (11258672518044817/1000000000000000000)
  q := 172
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14792]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14792]

theorem width_14793 : mW 14793 = 393728543593561 := by
  have hu : mW 14793 ≤ 393728543593561 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14793 ≤ 393728543593560 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14793 : RowArithmetic 14793 (1101065302765997315309/1000000000000000000000000) (600783196151739053420671/1000000000000000000000000) (792260875296857/125000000000000000000000) where
  r0 := (27789812621/50000000000000000)
  k0 := (3524492338137083/1000000000000000000)
  k6 := (5629145985535037/500000000000000000)
  q := (172005813855229905133/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14793]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14793]

theorem width_14794 : mW 14794 = 393821707005374 := by
  have hu : mW 14794 ≤ 393821707005374 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14794 ≤ 393821707005373 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14794 : RowArithmetic 14794 (1101039158858760165423/1000000000000000000000000) (7509662546216675511701/12500000000000000000000) (6336973577228507/1000000000000000000000000) where
  r0 := (22229595993/40000000000000000)
  k0 := (176215682907969/50000000000000000)
  k6 := (5497027081387/488281250000000)
  q := (10750726719622260029/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14794]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14794]

theorem width_14795 : mW 14795 = 393914886161961 := by
  have hu : mW 14795 ≤ 393914886161961 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14795 ≤ 393914886161960 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14795 : RowArithmetic 14795 (1101013020860095404599/1000000000000000000000000) (150190703151225157349741/250000000000000000000000) (6335860425499361/1000000000000000000000000) where
  r0 := (34730222297/62500000000000000)
  k0 := (3524134999316457/1000000000000000000)
  k6 := (5628765496434901/500000000000000000)
  q := (86008720488099344821/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14795]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14795]

theorem width_14796 : mW 14796 = 394008081064921 := by
  have hu : mW 14796 ≤ 394008081064921 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14796 ≤ 394008081064920 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14796 : RowArithmetic 14796 (1100986888768253735043/1000000000000000000000000) (600752622874147924424661/1000000000000000000000000) (6334747547101173/1000000000000000000000000) where
  r0 := (555627223199/1000000000000000000)
  k0 := (704791272321037/200000000000000000)
  k6 := (5628575280815617/500000000000000000)
  q := (86011627120988706477/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14796]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14796]

theorem width_14797 : mW 14797 = 394101291715850 := by
  have hu : mW 14797 ≤ 394101291715850 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14797 ≤ 394101291715849 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14797 : RowArithmetic 14797 (1100960762581487794569/1000000000000000000000000) (600742434504785156171959/1000000000000000000000000) (791704367743473/125000000000000000000000) where
  r0 := (138892724791/250000000000000000)
  k0 := (880944436255609/250000000000000000)
  k6 := (2251354033791671/200000000000000000)
  q := (172029067311312247317/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14797]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14797]

theorem width_14798 : mW 14798 = 394194518116343 := by
  have hu : mW 14798 ≤ 394194518116343 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14798 ≤ 394194518116342 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14798 : RowArithmetic 14798 (550467321149025653033/500000000000000000000000) (120146449499304322554149/200000000000000000000000) (6332522609953081/1000000000000000000000000) where
  r0 := (138878646161/250000000000000000)
  k0 := (880899787390477/250000000000000000)
  k6 := (11256389814844649/1000000000000000000)
  q := (86017440092111553143/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14798]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14798]

theorem width_14799 : mW 14799 = 394287760267998 := by
  have hu : mW 14799 ≤ 394287760267998 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14799 ≤ 394287760267997 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14799 : RowArithmetic 14799 (1100908527916197381607/1000000000000000000000000) (150180515462266680702091/250000000000000000000000) (6331410551030941/1000000000000000000000000) where
  r0 := (555458279637/1000000000000000000)
  k0 := (3523420575220471/1000000000000000000)
  k6 := (11256009499283603/1000000000000000000)
  q := (3440813857214598001/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14799]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14799]

theorem width_14800 : mW 14800 = 394381018172411 := by
  have hu : mW 14800 ≤ 394381018172411 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14800 ≤ 394381018172410 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14800 : RowArithmetic 14800 (1100882419434180642217/1000000000000000000000000) (37544492347633122005009/62500000000000000000000) (6330298765095303/1000000000000000000000000) where
  r0 := (27770099207/50000000000000000)
  k0 := (3523242021991819/1000000000000000000)
  k6 := (351738413195897/31250000000000000)
  q := (34409301068170507087/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14800]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14800]

theorem width_14801 : mW 14801 = 394474291831179 := by
  have hu : mW 14801 ≤ 394474291831179 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14801 ≤ 394474291831178 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14801 : RowArithmetic 14801 (34401759901570498307/31250000000000000000000) (600701694635420804034561/1000000000000000000000000) (6329187252060127/1000000000000000000000000) where
  r0 := (69418212269/125000000000000000)
  k0 := (440382936234499/125000000000000000)
  k6 := (5627624491896721/500000000000000000)
  q := (34410463524922183181/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14801]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14801]

theorem width_14802 : mW 14802 = 394567581245899 := by
  have hu : mW 14802 ≤ 394567581245899 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14802 ≤ 394567581245898 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14802 : RowArithmetic 14802 (1100830220162678810959/1000000000000000000000000) (37543219566790560408191/62500000000000000000000) (3164038005919703/500000000000000000000000) where
  r0 := (555289421671/1000000000000000000)
  k0 := (1761442489434927/500000000000000000)
  k6 := (11254868783851307/1000000000000000000)
  q := (172058129712024941563/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14802]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14802]

theorem width_14803 : mW 14803 = 394660886418167 := by
  have hu : mW 14803 ≤ 394660886418167 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14803 ≤ 394660886418166 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14803 : RowArithmetic 14803 (550402064684852919723/500000000000000000000000) (60068133286152418242651/100000000000000000000000) (6326965044347183/1000000000000000000000000) where
  r0 := (277616577347/500000000000000000)
  k0 := (3522706488967099/1000000000000000000)
  k6 := (11254488622435791/1000000000000000000)
  q := (43015985400778627287/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14803]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14803]

theorem width_14804 : mW 14804 = 394754207349581 := by
  have hu : mW 14804 ≤ 394754207349581 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14804 ≤ 394754207349580 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14804 : RowArithmetic 14804 (1100778044469593446697/1000000000000000000000000) (75083894251719526795839/125000000000000000000000) (3162927174748751/500000000000000000000000) where
  r0 := (277588448609/500000000000000000)
  k0 := (440316002520177/125000000000000000)
  k6 := (2813527124885097/250000000000000000)
  q := (172069753297899512041/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14804]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14804]

theorem width_14805 : mW 14805 = 394847544041737 := by
  have hu : mW 14805 ≤ 394847544041737 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14805 ≤ 394847544041736 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14805 : RowArithmetic 14805 (1100751965460599553791/1000000000000000000000000) (600660976525055030111237/1000000000000000000000000) (3162371963602237/500000000000000000000000) where
  r0 := (277560324621/500000000000000000)
  k0 := (88058739311321/25000000000000000)
  k6 := (11253728415158593/1000000000000000000)
  q := (21509445599549980033/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14805]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14805]

theorem width_14806 : mW 14806 = 394940896496233 := by
  have hu : mW 14806 ≤ 394940896496233 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14806 ≤ 394940896496232 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14806 : RowArithmetic 14806 (275181473085245473853/250000000000000000000000) (75081350049391315700689/125000000000000000000000) (1580908444345553/250000000000000000000000) where
  r0 := (138766102691/250000000000000000)
  k0 := (440271393229779/125000000000000000)
  k6 := (11253348369283903/1000000000000000000)
  q := (134438575077058891/781250000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14806]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14806]

theorem width_14807 : mW 14807 = 395034264714664 := by
  have hu : mW 14807 ≤ 395034264714664 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14807 ≤ 395034264714663 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14807 : RowArithmetic 14807 (1100699825109000132957/1000000000000000000000000) (120128125124738568980417/200000000000000000000000) (632252389994491/100000000000000000000000) where
  r0 := (27750409089/50000000000000000)
  k0 := (1760996370154053/500000000000000000)
  k6 := (5626484180954909/500000000000000000)
  q := (21510898400578251999/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14807]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14807]

theorem width_14808 : mW 14808 = 395127648698629 := by
  have hu : mW 14808 ≤ 395127648698629 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14808 ≤ 395127648698628 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14808 : RowArithmetic 14808 (1100673763762912896409/1000000000000000000000000) (75078806526306516367669/125000000000000000000000) (1580353573701683/250000000000000000000000) where
  r0 := (55495196229/100000000000000000)
  k0 := (3521814355865667/1000000000000000000)
  k6 := (2250517678605967/200000000000000000)
  q := (688371992457566507/4000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14808]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14808]

theorem width_14809 : mW 14809 = 395221048449725 := by
  have hu : mW 14809 ≤ 395221048449725 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14809 ≤ 395221048449724 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14809 : RowArithmetic 14809 (550323854150490159733/500000000000000000000000) (600620280155118577019077/1000000000000000000000000) (6320304961881909/1000000000000000000000000) where
  r0 := (55489575229/100000000000000000)
  k0 := (1760817996250713/500000000000000000)
  k6 := (5626104231318729/500000000000000000)
  q := (34419761765590417869/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14809]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14809]

theorem width_14810 : mW 14810 = 395314463969548 := by
  have hu : mW 14810 ≤ 395314463969548 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14810 ≤ 395314463969547 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14810 : RowArithmetic 14810 (550310829360731807851/500000000000000000000000) (600610109457402568622703/1000000000000000000000000) (6319195901084721/1000000000000000000000000) where
  r0 := (277419775889/500000000000000000)
  k0 := (3521457650212239/1000000000000000000)
  k6 := (2812957142681547/250000000000000000)
  q := (43026154836331819253/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14810]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14810]

theorem width_14811 : mW 14811 = 395407895259696 := by
  have hu : mW 14811 ≤ 395407895259696 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14811 ≤ 395407895259695 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14811 : RowArithmetic 14811 (550297807511311906173/500000000000000000000000) (600599940117014435308863/1000000000000000000000000) (6318087112329449/1000000000000000000000000) where
  r0 := (34673960047/62500000000000000)
  k0 := (3521279328994961/1000000000000000000)
  k6 := (2812862179322383/250000000000000000)
  q := (86055214833268529817/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14811]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14811]

theorem width_14812 : mW 14812 = 395501342321766 := by
  have hu : mW 14812 ≤ 395501342321766 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14812 ≤ 395501342321765 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14812 : RowArithmetic 14812 (275142394300680754049/250000000000000000000000) (600589772133664765241481/1000000000000000000000000) (3158489297765213/500000000000000000000000) where
  r0 := (554727179211/1000000000000000000)
  k0 := (176055051442481/50000000000000000)
  k6 := (11251068902320993/1000000000000000000)
  q := (172116239791601303737/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14812]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14812]

theorem width_14813 : mW 14813 = 395594805157356 := by
  have hu : mW 14813 ≤ 395594805157356 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14813 ≤ 395594805157355 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14813 : RowArithmetic 14813 (220108709052004713949/200000000000000000000000) (600579605507064063953497/1000000000000000000000000) (6315870350602001/1000000000000000000000000) where
  r0 := (554671007151/1000000000000000000)
  k0 := (1760461374883361/500000000000000000)
  k6 := (11250689125814081/1000000000000000000)
  q := (86061024860269936249/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14813]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14813]

theorem width_14814 : mW 14814 = 395688283768062 := by
  have hu : mW 14814 ≤ 395688283768062 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14814 ≤ 395688283768061 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14814 : RowArithmetic 14814 (137564689899098664409/125000000000000000000000) (6005694402369230100357/10000000000000000000000) (1578690594364647/250000000000000000000000) where
  r0 := (55461484457/100000000000000000)
  k0 := (1760372245871559/500000000000000000)
  k6 := (87893042091893/7812500000000000)
  q := (172127859453372625737/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14814]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14814]

theorem width_14815 : mW 14815 = 395781778155483 := by
  have hu : mW 14815 ≤ 395781778155483 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14815 ≤ 395781778155482 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14815 : RowArithmetic 14815 (1100491498999283487727/1000000000000000000000000) (300279638161476179462709/500000000000000000000000) (631365467601459/100000000000000000000000) where
  r0 := (554558691467/1000000000000000000)
  k0 := (220035390923677/62500000000000000)
  k6 := (11249929688159173/1000000000000000000)
  q := (86066834495059709963/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14815]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14815]

theorem width_14816 : mW 14816 = 395875288321216 := by
  have hu : mW 14816 ≤ 395875288321216 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14816 ≤ 395875288321215 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14816 : RowArithmetic 14816 (1100465484677770821201/1000000000000000000000000) (300274556882431483300253/500000000000000000000000) (789068405773059/125000000000000000000000) where
  r0 := (277251273919/500000000000000000)
  k0 := (3520388038864367/1000000000000000000)
  k6 := (11249550026998201/1000000000000000000)
  q := (34427895666160021637/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14816]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14816]

theorem width_14817 : mW 14817 = 395968814266859 := by
  have hu : mW 14817 ≤ 395968814266859 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14817 ≤ 395968814266858 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14817 : RowArithmetic 14817 (1100439476226516284863/1000000000000000000000000) (7506736907029571226289/12500000000000000000000) (39446500549267/6250000000000000000000) where
  r0 := (277223206841/500000000000000000)
  k0 := (3437704925781/976562500000000)
  k6 := (112491704042729/10000000000000000)
  q := (34429057495086908057/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14817]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14817]

theorem width_14818 : mW 14818 = 396062355994008 := by
  have hu : mW 14818 ≤ 396062355994008 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14818 ≤ 396062355994007 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14818 : RowArithmetic 14818 (34387921051368323283/31250000000000000000000) (24021151708606863527179/40000000000000000000000) (6310333201023883/1000000000000000000000000) where
  r0 := (554390288997/1000000000000000000)
  k0 := (880007917545453/250000000000000000)
  k6 := (5624395409988393/500000000000000000)
  q := (86075548212021281323/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14818]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14818]

theorem width_14819 : mW 14819 = 396155913504263 := by
  have hu : mW 14819 ≤ 396155913504263 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14819 ≤ 396155913504262 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14819 : RowArithmetic 14819 (68774217307990402571/62500000000000000000000) (300259317111495842590847/500000000000000000000000) (3154613292761241/500000000000000000000000) where
  r0 := (554334173779/1000000000000000000)
  k0 := (1759926758700533/500000000000000000)
  k6 := (11248411274103377/1000000000000000000)
  q := (86078452588322009171/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14819]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14819]

theorem width_14820 : mW 14820 = 396249486799219 := by
  have hu : mW 14820 ≤ 396249486799219 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14820 ≤ 396249486799218 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14820 : RowArithmetic 14820 (550180743038482385127/500000000000000000000000) (120101695417107452648171/200000000000000000000000) (126162404825863/20000000000000000000000) where
  r0 := (138569517007/250000000000000000)
  k0 := (3519675385660701/1000000000000000000)
  k6 := (11248031766646189/1000000000000000000)
  q := (172162713733258747097/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14820]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14820]

theorem width_14821 : mW 14821 = 396343075880476 := by
  have hu : mW 14821 ≤ 396343075880476 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14821 ≤ 396343075880475 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14821 : RowArithmetic 14821 (1100335501089408082557/1000000000000000000000000) (600498321302519424116557/1000000000000000000000000) (3153507084125237/500000000000000000000000) where
  r0 := (554221971741/1000000000000000000)
  k0 := (3519497274954387/1000000000000000000)
  k6 := (1405956537199843/125000000000000000)
  q := (172168522093906585291/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14821]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14821]

theorem width_14822 : mW 14822 = 396436680749631 := by
  have hu : mW 14822 ≤ 396436680749631 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14822 ≤ 396436680749630 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14822 : RowArithmetic 14822 (550154760981722521979/500000000000000000000000) (600488166873649617751053/1000000000000000000000000) (1576477091577281/250000000000000000000000) where
  r0 := (110833176983/200000000000000000)
  k0 := (351931918527579/100000000000000000)
  k6 := (5623636433477281/500000000000000000)
  q := (172174330258607365957/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14822]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14822]

theorem width_14823 : mW 14823 = 396530301408282 := by
  have hu : mW 14823 ≤ 396530301408282 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14823 ≤ 396530301408281 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14823 : RowArithmetic 14823 (550141774348672277259/500000000000000000000000) (600478013798639250003661/1000000000000000000000000) (1260960567076757/200000000000000000000000) where
  r0 := (138527451887/250000000000000000)
  k0 := (1759570558310877/500000000000000000)
  k6 := (11246893474707167/1000000000000000000)
  q := (172180138227380918781/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14823]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14823]

theorem width_14824 : mW 14824 = 396623937858027 := by
  have hu : mW 14824 ≤ 396623937858027 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14824 ≤ 396623937858026 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14824 : RowArithmetic 14824 (275064395322344042123/250000000000000000000000) (600467862077199806496811/1000000000000000000000000) (6303697575389179/1000000000000000000000000) where
  r0 := (277026869819/500000000000000000)
  k0 := (3518963068989117/1000000000000000000)
  k6 := (11246514120850083/1000000000000000000)
  q := (172185946000247070107/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14824]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14824]

theorem width_14825 : mW 14825 = 396717590100464 := by
  have hu : mW 14825 ≤ 396717590100464 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14825 ≤ 396717590100463 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14825 : RowArithmetic 14825 (1100231619737810094011/1000000000000000000000000) (600457711709042888022479/1000000000000000000000000) (6302592586240059/1000000000000000000000000) where
  r0 := (553997681183/1000000000000000000)
  k0 := (3518785042374719/1000000000000000000)
  k6 := (2811533701344209/250000000000000000)
  q := (34438350715445128587/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14825]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14825]

theorem width_14826 : mW 14826 = 396811258137191 := by
  have hu : mW 14826 ≤ 396811258137191 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14826 ≤ 396811258137190 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14826 : RowArithmetic 14826 (27505141601022929819/25000000000000000000000) (30022378134694007944341/50000000000000000000000) (6301487867851213/1000000000000000000000000) where
  r0 := (553941632181/1000000000000000000)
  k0 := (3518607036775399/1000000000000000000)
  k6 := (11245755528280953/1000000000000000000)
  q := (172197560958336456921/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14826]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14826]

theorem width_14827 : mW 14827 = 396904941969806 := by
  have hu : mW 14827 ≤ 396904941969806 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14827 ≤ 396904941969805 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14827 : RowArithmetic 14827 (1100179714196968979661/1000000000000000000000000) (600437415031423401456363/1000000000000000000000000) (6300383420137461/1000000000000000000000000) where
  r0 := (553885592629/1000000000000000000)
  k0 := (1759214526092409/500000000000000000)
  k6 := (11245376289555963/1000000000000000000)
  q := (172203368143599328381/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14827]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14827]

theorem width_14828 : mW 14828 = 396998641599907 := by
  have hu : mW 14828 ≤ 396998641599907 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14828 ≤ 396998641599906 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14828 : RowArithmetic 14828 (550076885102118811277/500000000000000000000000) (600427268721384433647029/1000000000000000000000000) (3149639621506829/500000000000000000000000) where
  r0 := (22153182501/40000000000000000)
  k0 := (3518251088599811/1000000000000000000)
  k6 := (11244997089195397/1000000000000000000)
  q := (10763073445814629393/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14828]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14828]

theorem width_14829 : mW 14829 = 397092357029092 := by
  have hu : mW 14829 ≤ 397092357029092 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14829 ≤ 397092357029091 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14829 : RowArithmetic 14829 (550063916030497970939/500000000000000000000000) (600417123763475237060177/1000000000000000000000000) (1574543834098673/250000000000000000000000) where
  r0 := (553773541867/1000000000000000000)
  k0 := (3518073146017213/1000000000000000000)
  k6 := (2811154481798197/250000000000000000)
  q := (43053745481665123069/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14829]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14829]

theorem width_14830 : mW 14830 = 397186088258960 := by
  have hu : mW 14830 ≤ 397186088258960 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14830 ≤ 397186088258959 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14830 : RowArithmetic 14830 (1100101899765516991799/1000000000000000000000000) (120081396031481553368023/200000000000000000000000) (629707170019547/100000000000000000000000) where
  r0 := (138429382663/250000000000000000)
  k0 := (3517895224430683/1000000000000000000)
  k6 := (2811059700885417/250000000000000000)
  q := (86110394262249200319/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14830]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14830]

theorem width_14831 : mW 14831 = 397279835291109 := by
  have hu : mW 14831 ≤ 397279835291109 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14831 ≤ 397279835291108 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14831 : RowArithmetic 14831 (275018993329018724373/250000000000000000000000) (30019841895144708054723/50000000000000000000000) (3147984167165473/500000000000000000000000) where
  r0 := (553661528879/1000000000000000000)
  k0 := (879429330960057/250000000000000000)
  k6 := (11243859718235573/1000000000000000000)
  q := (21528324365820949791/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14831]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14831]

theorem width_14832 : mW 14832 = 397373598127138 := by
  have hu : mW 14832 ≤ 397373598127138 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14832 ≤ 397373598127137 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14832 : RowArithmetic 14832 (275012513177736004387/250000000000000000000000) (300193348499823276725611/500000000000000000000000) (6294865238716093/1000000000000000000000000) where
  r0 := (276802768273/500000000000000000)
  k0 := (87938486106067/25000000000000000)
  k6 := (281087016781701/25000000000000000)
  q := (34446480226577576993/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14832]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14832]

theorem width_14833 : mW 14833 = 397467376768644 := by
  have hu : mW 14833 ≤ 397467376768644 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14833 ≤ 397467376768643 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14833 : RowArithmetic 14833 (1100024137948400198667/1000000000000000000000000) (600376557447377281155521/1000000000000000000000000) (125875248265319/20000000000000000000000) where
  r0 := (553549553649/1000000000000000000)
  k0 := (3517361585628517/1000000000000000000)
  k6 := (5621550831316303/500000000000000000)
  q := (86119103571739528413/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14833]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14833]

theorem width_14834 : mW 14834 = 397561171217226 := by
  have hu : mW 14834 ≤ 397561171217226 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14834 ≤ 397561171217225 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14834 : RowArithmetic 14834 (549999114513359551051/500000000000000000000000) (600366419245798634268573/1000000000000000000000000) (1258531971579111/200000000000000000000000) where
  r0 := (553493580187/1000000000000000000)
  k0 := (3517183747997743/1000000000000000000)
  k6 := (11242722692322811/1000000000000000000)
  q := (21530501619795113357/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14834]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14834]

theorem width_14835 : mW 14835 = 397654981474483 := by
  have hu : mW 14835 ≤ 397654981474483 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14835 ≤ 397654981474482 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14835 : RowArithmetic 14835 (1099972325944177040457/1000000000000000000000000) (300178141197311542855773/500000000000000000000000) (6291557572519983/1000000000000000000000000) where
  r0 := (553437616157/1000000000000000000)
  k0 := (3517005931344011/1000000000000000000)
  k6 := (11242343760332197/1000000000000000000)
  q := (86124909288776612331/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14835]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14835]

theorem width_14836 : mW 14836 = 397748807542014 := by
  have hu : mW 14836 ≤ 397748807542014 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14836 ≤ 397748807542013 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14836 : RowArithmetic 14836 (13749330358738137217/12500000000000000000000) (120069229378712625208411/200000000000000000000000) (6290455557054339/1000000000000000000000000) where
  r0 := (276690830779/500000000000000000)
  k0 := (879207033916831/250000000000000000)
  k6 := (11241964866654307/1000000000000000000)
  q := (43063906000268949129/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14836]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14836]

theorem width_14837 : mW 14837 = 397842649421417 := by
  have hu : mW 14837 ≤ 397842649421417 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14837 ≤ 397842649421416 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14837 : RowArithmetic 14837 (1099920537289618944559/1000000000000000000000000) (300168006371165692270389/500000000000000000000000) (6289353811413781/1000000000000000000000000) where
  r0 := (276662858193/500000000000000000)
  k0 := (439581295119769/125000000000000000)
  k6 := (2810396502820671/250000000000000000)
  q := (43065357307237101339/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14837]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14837]

theorem width_14838 : mW 14838 = 397936507114290 := by
  have hu : mW 14838 ≤ 397936507114290 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14838 ≤ 397936507114289 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14838 : RowArithmetic 14838 (1099894651714159623539/1000000000000000000000000) (120065175988128100707857/200000000000000000000000) (6288252335513497/1000000000000000000000000) where
  r0 := (553269780641/1000000000000000000)
  k0 := (3516472607219677/1000000000000000000)
  k6 := (89929657553687/8000000000000000)
  q := (43066808565297707697/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14838]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14838]

theorem width_14839 : mW 14839 = 398030380622233 := by
  have hu : mW 14839 ≤ 398030380622233 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14839 ≤ 398030380622232 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14839 : RowArithmetic 14839 (21997375439419030221/20000000000000000000000) (586245848133011072091/976562500000000000000) (6287151129268679/1000000000000000000000000) where
  r0 := (553213854319/1000000000000000000)
  k0 := (1758147437221183/500000000000000000)
  k6 := (11240828415432427/1000000000000000000)
  q := (43068259774455712271/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14839]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14839]

theorem width_14840 : mW 14840 = 398124269946844 := by
  have hu : mW 14840 ≤ 398124269946844 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14840 ≤ 398124269946843 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14840 : RowArithmetic 14840 (219968579611654917617/200000000000000000000000) (300152809192366312039177/500000000000000000000000) (3143025096297291/500000000000000000000000) where
  r0 := (553157937419/1000000000000000000)
  k0 := (3516117162626219/1000000000000000000)
  k6 := (1405056209367611/125000000000000000)
  q := (34455768747772846637/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14840]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14840]

theorem width_14841 : mW 14841 = 398218175089722 := by
  have hu : mW 14841 ≤ 398218175089722 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14841 ≤ 398218175089721 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14841 : RowArithmetic 14841 (43992681198976362707/40000000000000000000000) (300147744814970695505529/500000000000000000000000) (6284949525406481/1000000000000000000000000) where
  r0 := (276551014969/500000000000000000)
  k0 := (43949243397061/12500000000000000)
  k6 := (11240070972729809/1000000000000000000)
  q := (1722846481843347527/10000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14841]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14841]

theorem width_14842 : mW 14842 = 398312096052466 := by
  have hu : mW 14842 ≤ 398312096052466 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14842 ≤ 398312096052465 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14842 : RowArithmetic 14842 (137473895964704476497/125000000000000000000000) (600285362223542618449767/1000000000000000000000000) (3141924563809841/500000000000000000000000) where
  r0 := (553046131873/1000000000000000000)
  k0 := (351576180185199/100000000000000000)
  k6 := (11239692308792743/1000000000000000000)
  q := (17229045243425417391/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14842]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14842]

theorem width_14843 : mW 14843 = 398406032836675 := by
  have hu : mW 14843 ≤ 398406032836675 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14843 ≤ 398406032836674 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14843 : RowArithmetic 14843 (68735331955389770747/62500000000000000000000) (600275236165249492686981/1000000000000000000000000) (3141374499574763/500000000000000000000000) where
  r0 := (69123780403/125000000000000000)
  k0 := (1757792076445363/500000000000000000)
  k6 := (11239313683123241/1000000000000000000)
  q := (43074064122160564941/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14843]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14843]

theorem width_14844 : mW 14844 = 398499985443948 := by
  have hu : mW 14844 ≤ 398499985443948 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14844 ≤ 398499985443947 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14844 : RowArithmetic 14844 (1099739460678492787061/1000000000000000000000000) (300132555727387531315753/500000000000000000000000) (6281649139911387/1000000000000000000000000) where
  r0 := (552934363987/1000000000000000000)
  k0 := (878851631217887/250000000000000000)
  k6 := (561946754785743/50000000000000000)
  q := (43075515086879692471/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14844]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14844]

theorem width_14845 : mW 14845 = 398593953875884 := by
  have hu : mW 14845 ≤ 398593953875884 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14845 ≤ 398593953875883 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14845 : RowArithmetic 14845 (549856807946343992469/500000000000000000000000) (75031873511479088992193/125000000000000000000000) (24533396678987/3906250000000000000000) where
  r0 := (6910981177/12500000000000000)
  k0 := (3515228917791273/1000000000000000000)
  k6 := (2809639136640289/250000000000000000)
  q := (43076966002725865141/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14845]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14845]

theorem width_14846 : mW 14846 = 398687938134082 := by
  have hu : mW 14846 ≤ 398687938134082 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14846 ≤ 398687938134081 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14846 : RowArithmetic 14846 (274921944231776345269/250000000000000000000000) (600244866076135759330539/1000000000000000000000000) (6279450228792821/1000000000000000000000000) where
  r0 := (552822633741/1000000000000000000)
  k0 := (878762832911679/250000000000000000)
  k6 := (11238178035655687/1000000000000000000)
  q := (172313667478816084771/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14846]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14846]

theorem width_14847 : mW 14847 = 398781938220142 := by
  have hu : mW 14847 ≤ 398781938220142 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14847 ≤ 398781938220141 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14847 : RowArithmetic 14847 (1099661943780028662743/1000000000000000000000000) (73270842945238969141/122070312500000000000) (6278351176743291/1000000000000000000000000) where
  r0 := (552766782729/1000000000000000000)
  k0 := (219679610402367/62500000000000000)
  k6 := (11237799562992011/1000000000000000000)
  q := (34463894150255278429/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14847]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14847]

theorem width_14848 : mW 14848 = 398875954135662 := by
  have hu : mW 14848 ≤ 398875954135662 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14848 ≤ 398875954135661 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14848 : RowArithmetic 14848 (549818058224871498153/500000000000000000000000) (300112313042665947693239/500000000000000000000000) (6277252393587607/1000000000000000000000000) where
  r0 := (552710941119/1000000000000000000)
  k0 := (219668513884501/62500000000000000)
  k6 := (11237421128563691/1000000000000000000)
  q := (172325273828304129001/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14848]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14848]

theorem width_14849 : mW 14849 = 398969985882242 := by
  have hu : mW 14849 ≤ 398969985882242 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14849 ≤ 398969985882241 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14849 : RowArithmetic 14849 (1099610294934533363499/1000000000000000000000000) (600214508109652107098021/1000000000000000000000000) (6276153879241291/1000000000000000000000000) where
  r0 := (34540944307/62500000000000000)
  k0 := (1757259349397749/500000000000000000)
  k6 := (11237042732364289/1000000000000000000)
  q := (172331076709919038329/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14849]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14849]

theorem width_14850 : mW 14850 = 399064033461481 := by
  have hu : mW 14850 ≤ 399064033461481 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14850 ≤ 399064033461480 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14850 : RowArithmetic 14850 (68724029952042863037/62500000000000000000000) (300102195740036013984291/500000000000000000000000) (6275055633619917/1000000000000000000000000) where
  r0 := (552599286103/1000000000000000000)
  k0 := (439292649544449/125000000000000000)
  k6 := (11236664374387369/1000000000000000000)
  q := (43084219849035214949/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14850]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14850]

theorem width_14851 : mW 14851 = 399158096874979 := by
  have hu : mW 14851 ≤ 399158096874979 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14851 ≤ 399158096874978 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14851 : RowArithmetic 14851 (549779334671243303507/500000000000000000000000) (600194276196305360558581/1000000000000000000000000) (6273957656639077/1000000000000000000000000) where
  r0 := (552543472691/1000000000000000000)
  k0 := (1757081857416143/500000000000000000)
  k6 := (175566969603539/15625000000000000)
  q := (34468536377397865949/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14851]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14851]

theorem width_14852 : mW 14852 = 399252176124335 := by
  have hu : mW 14852 ≤ 399252176124335 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14852 ≤ 399252176124334 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14852 : RowArithmetic 14852 (43981314610488923831/40000000000000000000000) (37511510141129123372689/62500000000000000000000) (627285994821441/100000000000000000000000) where
  r0 := (22099506747/40000000000000000)
  k0 := (351398625422557/100000000000000000)
  k6 := (11235907773075237/1000000000000000000)
  q := (86174242091242090599/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14852]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14852]

theorem width_14853 : mW 14853 = 399346271211149 := by
  have hu : mW 14853 ≤ 399346271211149 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14853 ≤ 399346271211148 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14853 : RowArithmetic 14853 (549753533495091421369/500000000000000000000000) (18755439052033371115531/31250000000000000000000) (6271762508261573/1000000000000000000000000) where
  r0 := (11048637481/20000000000000000)
  k0 := (439226101815339/125000000000000000)
  k6 := (11235529529727161/1000000000000000000)
  q := (172354286282645143853/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14853]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14853]

theorem width_14854 : mW 14854 = 399440382137019 := by
  have hu : mW 14854 ≤ 399440382137019 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14854 ≤ 399440382137018 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14854 : RowArithmetic 14854 (68717579657790930689/62500000000000000000000) (600163938417025006663873/1000000000000000000000000) (195958291771759/31250000000000000000000) where
  r0 := (34523505551/62500000000000000)
  k0 := (3513631395726877/1000000000000000000)
  k6 := (11235151324575839/1000000000000000000)
  q := (172360088187491944089/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14854]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14854]

theorem width_14855 : mW 14855 = 399534508903547 := by
  have hu : mW 14855 ≤ 399534508903547 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14855 ≤ 399534508903546 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14855 : RowArithmetic 14855 (219891097572785454049/200000000000000000000000) (300076914256825765867359/500000000000000000000000) (6269568433434247/1000000000000000000000000) where
  r0 := (552320312971/1000000000000000000)
  k0 := (3513453997834873/1000000000000000000)
  k6 := (11234773157614841/1000000000000000000)
  q := (34473177979408860993/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14855]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14855]

theorem width_14856 : mW 14856 = 399628651512330 := by
  have hu : mW 14856 ≤ 399628651512330 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14856 ≤ 399628651512329 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14856 : RowArithmetic 14856 (274857426751572682053/250000000000000000000000) (600143719954661672995787/1000000000000000000000000) (3134235899195627/500000000000000000000000) where
  r0 := (552264546511/1000000000000000000)
  k0 := (3513276620837143/1000000000000000000)
  k6 := (5617197514418871/500000000000000000)
  q := (172371691411321946221/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14856]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14856]

theorem width_14857 : mW 14857 = 399722809964970 := by
  have hu : mW 14857 ≤ 399722809964970 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14857 ≤ 399722809964969 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14857 : RowArithmetic 14857 (68712745746877161569/62500000000000000000000) (600133612739769605026717/1000000000000000000000000) (6267375431483067/1000000000000000000000000) where
  r0 := (110441757887/200000000000000000)
  k0 := (351309926473367/100000000000000000)
  k6 := (2246803387647623/200000000000000000)
  q := (172377492730344584277/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14857]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14857]

theorem width_14858 : mW 14858 = 399816984263066 := by
  have hu : mW 14858 ≤ 399816984263066 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14858 ≤ 399816984263065 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14858 : RowArithmetic 14858 (549689081346725024541/500000000000000000000000) (300061753434344871996373/500000000000000000000000) (3133139666312763/500000000000000000000000) where
  r0 := (27607652087/50000000000000000)
  k0 := (878230482379519/250000000000000000)
  k6 := (87762803795387/7812500000000000)
  q := (43095823463532983059/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14858]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14858]

theorem width_14859 : mW 14859 = 399911174408217 := by
  have hu : mW 14859 ≤ 399911174408217 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14859 ≤ 399911174408216 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14859 : RowArithmetic 14859 (109935239923482897207/100000000000000000000000) (600113402341136554647343/1000000000000000000000000) (6265183501734501/1000000000000000000000000) where
  r0 := (22083892137/40000000000000000)
  k0 := (3512744615190343/1000000000000000000)
  k6 := (702078804471599/62500000000000000)
  q := (86194547391351849943/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14859]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14859]

theorem width_14860 : mW 14860 = 400005380402024 := by
  have hu : mW 14860 ≤ 400005380402024 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14860 ≤ 400005380402023 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14860 : RowArithmetic 14860 (1099326641572463022133/1000000000000000000000000) (600103299156824543909023/1000000000000000000000000) (6264087938725867/1000000000000000000000000) where
  r0 := (276020787243/500000000000000000)
  k0 := (3512567321740909/1000000000000000000)
  k6 := (5616441447719919/500000000000000000)
  q := (5387340484877487303/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14860]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14860]

theorem width_14861 : mW 14861 = 400099602246087 := by
  have hu : mW 14861 ≤ 400099602246087 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14861 ≤ 400099602246086 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14861 : RowArithmetic 14861 (1099300889704644925267/1000000000000000000000000) (300046598657734161572241/500000000000000000000000) (3131496321757773/500000000000000000000000) where
  r0 := (551985854923/1000000000000000000)
  k0 := (702478009834587/200000000000000000)
  k6 := (5616252478742939/500000000000000000)
  q := (172400696054279316823/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14861]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14861]

theorem width_14862 : mW 14862 = 400193839942005 := by
  have hu : mW 14862 ≤ 400193839942005 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14862 ≤ 400193839942004 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14862 : RowArithmetic 14862 (1099275143629668464281/1000000000000000000000000) (600083096816782565523461/1000000000000000000000000) (1565474404004877/250000000000000000000000) where
  r0 := (137982536183/250000000000000000)
  k0 := (439026599684607/125000000000000000)
  k6 := (11232127057677287/1000000000000000000)
  q := (34481299279464513821/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14862]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14862]

theorem width_14863 : mW 14863 = 400288093491378 := by
  have hu : mW 14863 ≤ 400288093491378 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14863 ≤ 400288093491377 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14863 : RowArithmetic 14863 (1099249403345827651323/1000000000000000000000000) (300036498830241030126001/500000000000000000000000) (6260802856153741/1000000000000000000000000) where
  r0 := (68984305489/125000000000000000)
  k0 := (70240711333053/20000000000000000)
  k6 := (350992162375239/31250000000000000)
  q := (172412296545229047071/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14863]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14863]

theorem width_14864 : mW 14864 = 400382362895807 := by
  have hu : mW 14864 ≤ 400382362895807 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14864 ≤ 400382362895806 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14864 : RowArithmetic 14864 (54961183442570836419/50000000000000000000000) (600062899846281694906489/1000000000000000000000000) (6259708363834253/1000000000000000000000000) where
  r0 := (27590937623/50000000000000000)
  k0 := (877964589173483/250000000000000000)
  k6 := (5615685686235273/500000000000000000)
  q := (34483619299603688787/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14864]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14864]

theorem width_14865 : mW 14865 = 400476648156892 := by
  have hu : mW 14865 ≤ 400476648156892 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14865 ≤ 400476648156891 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14865 : RowArithmetic 14865 (17174967814761421773/15625000000000000000000) (600052803373896352400049/1000000000000000000000000) (782326767372137/125000000000000000000000) where
  r0 := (275881535187/500000000000000000)
  k0 := (702336233519499/200000000000000000)
  k6 := (11230993587059569/1000000000000000000)
  q := (172423896255710449597/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14865]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14865]

theorem width_14866 : mW 14866 = 400570949276233 := by
  have hu : mW 14866 ≤ 400570949276233 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14866 ≤ 400570949276232 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14866 : RowArithmetic 14866 (549586108612033193421/500000000000000000000000) (150010677060760274160531/250000000000000000000000) (3128760090749179/500000000000000000000000) where
  r0 := (137926849413/250000000000000000)
  k0 := (877875999840033/250000000000000000)
  k6 := (2246123167953661/200000000000000000)
  q := (21553711977290593831/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14866]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14866]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 14792 then ⟨(110109145258355469167/100000000000000000000000), (938739671825635298183/1562500000000000000000), (1584800175256151/250000000000000000000000)⟩ else
  if n = 14793 then ⟨(1101065302765997315309/1000000000000000000000000), (600783196151739053420671/1000000000000000000000000), (792260875296857/125000000000000000000000)⟩ else
  if n = 14794 then ⟨(1101039158858760165423/1000000000000000000000000), (7509662546216675511701/12500000000000000000000), (6336973577228507/1000000000000000000000000)⟩ else
  if n = 14795 then ⟨(1101013020860095404599/1000000000000000000000000), (150190703151225157349741/250000000000000000000000), (6335860425499361/1000000000000000000000000)⟩ else
  if n = 14796 then ⟨(1100986888768253735043/1000000000000000000000000), (600752622874147924424661/1000000000000000000000000), (6334747547101173/1000000000000000000000000)⟩ else
  if n = 14797 then ⟨(1100960762581487794569/1000000000000000000000000), (600742434504785156171959/1000000000000000000000000), (791704367743473/125000000000000000000000)⟩ else
  if n = 14798 then ⟨(550467321149025653033/500000000000000000000000), (120146449499304322554149/200000000000000000000000), (6332522609953081/1000000000000000000000000)⟩ else
  if n = 14799 then ⟨(1100908527916197381607/1000000000000000000000000), (150180515462266680702091/250000000000000000000000), (6331410551030941/1000000000000000000000000)⟩ else
  if n = 14800 then ⟨(1100882419434180642217/1000000000000000000000000), (37544492347633122005009/62500000000000000000000), (6330298765095303/1000000000000000000000000)⟩ else
  if n = 14801 then ⟨(34401759901570498307/31250000000000000000000), (600701694635420804034561/1000000000000000000000000), (6329187252060127/1000000000000000000000000)⟩ else
  if n = 14802 then ⟨(1100830220162678810959/1000000000000000000000000), (37543219566790560408191/62500000000000000000000), (3164038005919703/500000000000000000000000)⟩ else
  if n = 14803 then ⟨(550402064684852919723/500000000000000000000000), (60068133286152418242651/100000000000000000000000), (6326965044347183/1000000000000000000000000)⟩ else
  if n = 14804 then ⟨(1100778044469593446697/1000000000000000000000000), (75083894251719526795839/125000000000000000000000), (3162927174748751/500000000000000000000000)⟩ else
  if n = 14805 then ⟨(1100751965460599553791/1000000000000000000000000), (600660976525055030111237/1000000000000000000000000), (3162371963602237/500000000000000000000000)⟩ else
  if n = 14806 then ⟨(275181473085245473853/250000000000000000000000), (75081350049391315700689/125000000000000000000000), (1580908444345553/250000000000000000000000)⟩ else
  if n = 14807 then ⟨(1100699825109000132957/1000000000000000000000000), (120128125124738568980417/200000000000000000000000), (632252389994491/100000000000000000000000)⟩ else
  if n = 14808 then ⟨(1100673763762912896409/1000000000000000000000000), (75078806526306516367669/125000000000000000000000), (1580353573701683/250000000000000000000000)⟩ else
  if n = 14809 then ⟨(550323854150490159733/500000000000000000000000), (600620280155118577019077/1000000000000000000000000), (6320304961881909/1000000000000000000000000)⟩ else
  if n = 14810 then ⟨(550310829360731807851/500000000000000000000000), (600610109457402568622703/1000000000000000000000000), (6319195901084721/1000000000000000000000000)⟩ else
  if n = 14811 then ⟨(550297807511311906173/500000000000000000000000), (600599940117014435308863/1000000000000000000000000), (6318087112329449/1000000000000000000000000)⟩ else
  if n = 14812 then ⟨(275142394300680754049/250000000000000000000000), (600589772133664765241481/1000000000000000000000000), (3158489297765213/500000000000000000000000)⟩ else
  if n = 14813 then ⟨(220108709052004713949/200000000000000000000000), (600579605507064063953497/1000000000000000000000000), (6315870350602001/1000000000000000000000000)⟩ else
  if n = 14814 then ⟨(137564689899098664409/125000000000000000000000), (6005694402369230100357/10000000000000000000000), (1578690594364647/250000000000000000000000)⟩ else
  if n = 14815 then ⟨(1100491498999283487727/1000000000000000000000000), (300279638161476179462709/500000000000000000000000), (631365467601459/100000000000000000000000)⟩ else
  if n = 14816 then ⟨(1100465484677770821201/1000000000000000000000000), (300274556882431483300253/500000000000000000000000), (789068405773059/125000000000000000000000)⟩ else
  if n = 14817 then ⟨(1100439476226516284863/1000000000000000000000000), (7506736907029571226289/12500000000000000000000), (39446500549267/6250000000000000000000)⟩ else
  if n = 14818 then ⟨(34387921051368323283/31250000000000000000000), (24021151708606863527179/40000000000000000000000), (6310333201023883/1000000000000000000000000)⟩ else
  if n = 14819 then ⟨(68774217307990402571/62500000000000000000000), (300259317111495842590847/500000000000000000000000), (3154613292761241/500000000000000000000000)⟩ else
  if n = 14820 then ⟨(550180743038482385127/500000000000000000000000), (120101695417107452648171/200000000000000000000000), (126162404825863/20000000000000000000000)⟩ else
  if n = 14821 then ⟨(1100335501089408082557/1000000000000000000000000), (600498321302519424116557/1000000000000000000000000), (3153507084125237/500000000000000000000000)⟩ else
  if n = 14822 then ⟨(550154760981722521979/500000000000000000000000), (600488166873649617751053/1000000000000000000000000), (1576477091577281/250000000000000000000000)⟩ else
  if n = 14823 then ⟨(550141774348672277259/500000000000000000000000), (600478013798639250003661/1000000000000000000000000), (1260960567076757/200000000000000000000000)⟩ else
  if n = 14824 then ⟨(275064395322344042123/250000000000000000000000), (600467862077199806496811/1000000000000000000000000), (6303697575389179/1000000000000000000000000)⟩ else
  if n = 14825 then ⟨(1100231619737810094011/1000000000000000000000000), (600457711709042888022479/1000000000000000000000000), (6302592586240059/1000000000000000000000000)⟩ else
  if n = 14826 then ⟨(27505141601022929819/25000000000000000000000), (30022378134694007944341/50000000000000000000000), (6301487867851213/1000000000000000000000000)⟩ else
  if n = 14827 then ⟨(1100179714196968979661/1000000000000000000000000), (600437415031423401456363/1000000000000000000000000), (6300383420137461/1000000000000000000000000)⟩ else
  if n = 14828 then ⟨(550076885102118811277/500000000000000000000000), (600427268721384433647029/1000000000000000000000000), (3149639621506829/500000000000000000000000)⟩ else
  if n = 14829 then ⟨(550063916030497970939/500000000000000000000000), (600417123763475237060177/1000000000000000000000000), (1574543834098673/250000000000000000000000)⟩ else
  if n = 14830 then ⟨(1100101899765516991799/1000000000000000000000000), (120081396031481553368023/200000000000000000000000), (629707170019547/100000000000000000000000)⟩ else
  if n = 14831 then ⟨(275018993329018724373/250000000000000000000000), (30019841895144708054723/50000000000000000000000), (3147984167165473/500000000000000000000000)⟩ else
  if n = 14832 then ⟨(275012513177736004387/250000000000000000000000), (300193348499823276725611/500000000000000000000000), (6294865238716093/1000000000000000000000000)⟩ else
  if n = 14833 then ⟨(1100024137948400198667/1000000000000000000000000), (600376557447377281155521/1000000000000000000000000), (125875248265319/20000000000000000000000)⟩ else
  if n = 14834 then ⟨(549999114513359551051/500000000000000000000000), (600366419245798634268573/1000000000000000000000000), (1258531971579111/200000000000000000000000)⟩ else
  if n = 14835 then ⟨(1099972325944177040457/1000000000000000000000000), (300178141197311542855773/500000000000000000000000), (6291557572519983/1000000000000000000000000)⟩ else
  if n = 14836 then ⟨(13749330358738137217/12500000000000000000000), (120069229378712625208411/200000000000000000000000), (6290455557054339/1000000000000000000000000)⟩ else
  if n = 14837 then ⟨(1099920537289618944559/1000000000000000000000000), (300168006371165692270389/500000000000000000000000), (6289353811413781/1000000000000000000000000)⟩ else
  if n = 14838 then ⟨(1099894651714159623539/1000000000000000000000000), (120065175988128100707857/200000000000000000000000), (6288252335513497/1000000000000000000000000)⟩ else
  if n = 14839 then ⟨(21997375439419030221/20000000000000000000000), (586245848133011072091/976562500000000000000), (6287151129268679/1000000000000000000000000)⟩ else
  if n = 14840 then ⟨(219968579611654917617/200000000000000000000000), (300152809192366312039177/500000000000000000000000), (3143025096297291/500000000000000000000000)⟩ else
  if n = 14841 then ⟨(43992681198976362707/40000000000000000000000), (300147744814970695505529/500000000000000000000000), (6284949525406481/1000000000000000000000000)⟩ else
  if n = 14842 then ⟨(137473895964704476497/125000000000000000000000), (600285362223542618449767/1000000000000000000000000), (3141924563809841/500000000000000000000000)⟩ else
  if n = 14843 then ⟨(68735331955389770747/62500000000000000000000), (600275236165249492686981/1000000000000000000000000), (3141374499574763/500000000000000000000000)⟩ else
  if n = 14844 then ⟨(1099739460678492787061/1000000000000000000000000), (300132555727387531315753/500000000000000000000000), (6281649139911387/1000000000000000000000000)⟩ else
  if n = 14845 then ⟨(549856807946343992469/500000000000000000000000), (75031873511479088992193/125000000000000000000000), (24533396678987/3906250000000000000000)⟩ else
  if n = 14846 then ⟨(274921944231776345269/250000000000000000000000), (600244866076135759330539/1000000000000000000000000), (6279450228792821/1000000000000000000000000)⟩ else
  if n = 14847 then ⟨(1099661943780028662743/1000000000000000000000000), (73270842945238969141/122070312500000000000), (6278351176743291/1000000000000000000000000)⟩ else
  if n = 14848 then ⟨(549818058224871498153/500000000000000000000000), (300112313042665947693239/500000000000000000000000), (6277252393587607/1000000000000000000000000)⟩ else
  if n = 14849 then ⟨(1099610294934533363499/1000000000000000000000000), (600214508109652107098021/1000000000000000000000000), (6276153879241291/1000000000000000000000000)⟩ else
  if n = 14850 then ⟨(68724029952042863037/62500000000000000000000), (300102195740036013984291/500000000000000000000000), (6275055633619917/1000000000000000000000000)⟩ else
  if n = 14851 then ⟨(549779334671243303507/500000000000000000000000), (600194276196305360558581/1000000000000000000000000), (6273957656639077/1000000000000000000000000)⟩ else
  if n = 14852 then ⟨(43981314610488923831/40000000000000000000000), (37511510141129123372689/62500000000000000000000), (627285994821441/100000000000000000000000)⟩ else
  if n = 14853 then ⟨(549753533495091421369/500000000000000000000000), (18755439052033371115531/31250000000000000000000), (6271762508261573/1000000000000000000000000)⟩ else
  if n = 14854 then ⟨(68717579657790930689/62500000000000000000000), (600163938417025006663873/1000000000000000000000000), (195958291771759/31250000000000000000000)⟩ else
  if n = 14855 then ⟨(219891097572785454049/200000000000000000000000), (300076914256825765867359/500000000000000000000000), (6269568433434247/1000000000000000000000000)⟩ else
  if n = 14856 then ⟨(274857426751572682053/250000000000000000000000), (600143719954661672995787/1000000000000000000000000), (3134235899195627/500000000000000000000000)⟩ else
  if n = 14857 then ⟨(68712745746877161569/62500000000000000000000), (600133612739769605026717/1000000000000000000000000), (6267375431483067/1000000000000000000000000)⟩ else
  if n = 14858 then ⟨(549689081346725024541/500000000000000000000000), (300061753434344871996373/500000000000000000000000), (3133139666312763/500000000000000000000000)⟩ else
  if n = 14859 then ⟨(109935239923482897207/100000000000000000000000), (600113402341136554647343/1000000000000000000000000), (6265183501734501/1000000000000000000000000)⟩ else
  if n = 14860 then ⟨(1099326641572463022133/1000000000000000000000000), (600103299156824543909023/1000000000000000000000000), (6264087938725867/1000000000000000000000000)⟩ else
  if n = 14861 then ⟨(1099300889704644925267/1000000000000000000000000), (300046598657734161572241/500000000000000000000000), (3131496321757773/500000000000000000000000)⟩ else
  if n = 14862 then ⟨(1099275143629668464281/1000000000000000000000000), (600083096816782565523461/1000000000000000000000000), (1565474404004877/250000000000000000000000)⟩ else
  if n = 14863 then ⟨(1099249403345827651323/1000000000000000000000000), (300036498830241030126001/500000000000000000000000), (6260802856153741/1000000000000000000000000)⟩ else
  if n = 14864 then ⟨(54961183442570836419/50000000000000000000000), (600062899846281694906489/1000000000000000000000000), (6259708363834253/1000000000000000000000000)⟩ else
  if n = 14865 then ⟨(17174967814761421773/15625000000000000000000), (600052803373896352400049/1000000000000000000000000), (782326767372137/125000000000000000000000)⟩ else
  ⟨(549586108612033193421/500000000000000000000000), (150010677060760274160531/250000000000000000000000), (3128760090749179/500000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14792 ≤ n) (hb : n ≤ 14866) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14792
  · exact row_14793
  · exact row_14794
  · exact row_14795
  · exact row_14796
  · exact row_14797
  · exact row_14798
  · exact row_14799
  · exact row_14800
  · exact row_14801
  · exact row_14802
  · exact row_14803
  · exact row_14804
  · exact row_14805
  · exact row_14806
  · exact row_14807
  · exact row_14808
  · exact row_14809
  · exact row_14810
  · exact row_14811
  · exact row_14812
  · exact row_14813
  · exact row_14814
  · exact row_14815
  · exact row_14816
  · exact row_14817
  · exact row_14818
  · exact row_14819
  · exact row_14820
  · exact row_14821
  · exact row_14822
  · exact row_14823
  · exact row_14824
  · exact row_14825
  · exact row_14826
  · exact row_14827
  · exact row_14828
  · exact row_14829
  · exact row_14830
  · exact row_14831
  · exact row_14832
  · exact row_14833
  · exact row_14834
  · exact row_14835
  · exact row_14836
  · exact row_14837
  · exact row_14838
  · exact row_14839
  · exact row_14840
  · exact row_14841
  · exact row_14842
  · exact row_14843
  · exact row_14844
  · exact row_14845
  · exact row_14846
  · exact row_14847
  · exact row_14848
  · exact row_14849
  · exact row_14850
  · exact row_14851
  · exact row_14852
  · exact row_14853
  · exact row_14854
  · exact row_14855
  · exact row_14856
  · exact row_14857
  · exact row_14858
  · exact row_14859
  · exact row_14860
  · exact row_14861
  · exact row_14862
  · exact row_14863
  · exact row_14864
  · exact row_14865
  · exact row_14866

end BstLean.Part271.R3.Rows14792
