import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 13457–13531. -/
namespace BstLean.Part271.R3.Rows13457
open Real BstLean.Part130 BstLean.Part227

theorem width_13457 : mW 13457 = 282695492233846 := by
  have hu : mW 13457 ≤ 282695492233846 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13457 ≤ 282695492233845 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13457 : RowArithmetic 13457 (285515839266318220917/250000000000000000000000) (615745201957948150932959/1000000000000000000000000) (8109185866272983/1000000000000000000000000) where
  r0 := (640586263223/1000000000000000000)
  k0 := (3783794786062539/1000000000000000000)
  k6 := (9221817859059/781250000000000)
  q := (164054868870143564539/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13457]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13457]

theorem width_13458 : mW 13458 = 282769024680399 := by
  have hu : mW 13458 ≤ 282769024680399 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13458 ≤ 282769024680398 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13458 : RowArithmetic 13458 (114202746062620118519/100000000000000000000000) (615732891370547773100539/1000000000000000000000000) (1013451827485783/125000000000000000000000) where
  r0 := (64051486617/100000000000000000)
  k0 := (1891791958626761/500000000000000000)
  k6 := (11803488304604393/1000000000000000000)
  q := (5126905133703958053/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13458]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13458]

theorem width_13459 : mW 13459 = 282842570787836 := by
  have hu : mW 13459 ≤ 282842570787836 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13459 ≤ 282842570787835 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13459 : RowArithmetic 13459 (1141991573134760988387/1000000000000000000000000) (307860291312341920175563/500000000000000000000000) (2026510949739859/250000000000000000000000) where
  r0 := (320221741189/500000000000000000)
  k0 := (1891686537930393/500000000000000000)
  k6 := (11803049798490947/1000000000000000000)
  q := (164067059460453547803/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13459]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13459]

theorem width_13460 : mW 13460 = 282916130557681 := by
  have hu : mW 13460 ≤ 282916130557681 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13460 ≤ 282916130557680 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13460 : RowArithmetic 13460 (1141955694588032348237/1000000000000000000000000) (12314165514398328552227/20000000000000000000000) (8104473403344587/1000000000000000000000000) where
  r0 := (128074422369/200000000000000000)
  k0 := (29555955170961/7812500000000000)
  k6 := (1475326417655763/125000000000000000)
  q := (4101828860398736821/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13460]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13460]

theorem width_13461 : mW 13461 = 282989703991457 := by
  have hu : mW 13461 ≤ 282989703991457 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13461 ≤ 282989703991456 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13461 : RowArithmetic 13461 (57095991249154863763/50000000000000000000000) (4810124770748482900029/7812500000000000000000) (8102903432893893/1000000000000000000000000) where
  r0 := (320150377283/500000000000000000)
  k0 := (378295147531/100000000000000)
  k6 := (11802172932860787/1000000000000000000)
  q := (20509906143129958263/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13461]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13461]

theorem width_13462 : mW 13462 = 283063291090686 := by
  have hu : mW 13462 ≤ 283063291090686 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13462 ≤ 283063291090685 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13462 : RowArithmetic 13462 (142735495539629966657/125000000000000000000000) (307841833715956164163869/500000000000000000000000) (4050666943729813/500000000000000000000000) where
  r0 := (640229410539/1000000000000000000)
  k0 := (756548143228087/200000000000000000)
  k6 := (5900867286662961/500000000000000000)
  q := (164085343647749356201/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13462]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13462]

theorem width_13463 : mW 13463 = 283136891856890 := by
  have hu : mW 13463 ≤ 283136891856890 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13463 ≤ 283136891856889 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13463 : RowArithmetic 13463 (1141848112586944901761/1000000000000000000000000) (615671366047796565137587/1000000000000000000000000) (4049882383447061/500000000000000000000000) where
  r0 := (640158079759/1000000000000000000)
  k0 := (3782529984364123/1000000000000000000)
  k6 := (5900648131316219/500000000000000000)
  q := (32818287584820753411/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13463]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13463]

theorem width_13464 : mW 13464 = 283210506291594 := by
  have hu : mW 13464 ≤ 283210506291594 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13464 ≤ 283210506291593 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13464 : RowArithmetic 13464 (570906134894948485213/500000000000000000000000) (307829533251509569435093/500000000000000000000000) (8098196071049693/1000000000000000000000000) where
  r0 := (40005422639/62500000000000000)
  k0 := (3782319279979733/1000000000000000000)
  k6 := (11800858000771267/1000000000000000000)
  q := (164097531974128117903/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13464]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13464]

theorem width_13465 : mW 13465 = 283284134396320 := by
  have hu : mW 13465 ≤ 283284134396320 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13465 ≤ 283284134396319 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13465 : RowArithmetic 13465 (1141776435922983551151/1000000000000000000000000) (12312935375942818271003/20000000000000000000000) (4048313899889403/500000000000000000000000) where
  r0 := (640015457931/1000000000000000000)
  k0 := (1891054301491489/500000000000000000)
  k6 := (590020989386667/50000000000000000)
  q := (20512953224730952913/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13465]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13465]

theorem width_13466 : mW 13466 = 283357776172590 := by
  have hu : mW 13466 ≤ 283357776172590 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13466 ≤ 283357776172589 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13466 : RowArithmetic 13466 (228348122196658693921/200000000000000000000000) (153908618232430709975259/250000000000000000000000) (4047529976466993/500000000000000000000000) where
  r0 := (319972083437/500000000000000000)
  k0 := (3781897953360707/1000000000000000000)
  k6 := (2359996324701919/200000000000000000)
  q := (164109719395287493131/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13466]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13466]

theorem width_13467 : mW 13467 = 283431431621928 := by
  have hu : mW 13467 ≤ 283431431621928 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13467 ≤ 283431431621927 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13467 : RowArithmetic 13467 (228340958993583059301/200000000000000000000000) (307811089450163000827149/500000000000000000000000) (809349253036777/100000000000000000000000) where
  r0 := (159968222263/250000000000000000)
  k0 := (3781687331114539/1000000000000000000)
  k6 := (1474942938511371/125000000000000000)
  q := (8205790638323646629/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13467]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13467]

theorem width_13468 : mW 13468 = 283505100745857 := by
  have hu : mW 13468 ≤ 283505100745857 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13468 ≤ 283505100745856 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13468 : RowArithmetic 13468 (114166898787393955129/100000000000000000000000) (615609886708511673168899/1000000000000000000000000) (1618385106386557/200000000000000000000000) where
  r0 := (639801624461/1000000000000000000)
  k0 := (3781476736237227/1000000000000000000)
  k6 := (11799105441468401/1000000000000000000)
  q := (82060952955714571083/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13468]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13468]

theorem width_13469 : mW 13469 = 283578783545901 := by
  have hu : mW 13469 ≤ 283578783545901 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13469 ≤ 283578783545900 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13469 : RowArithmetic 13469 (570816594849228616541/500000000000000000000000) (615597596353841239861843/1000000000000000000000000) (4045179478740847/500000000000000000000000) where
  r0 := (639730373097/1000000000000000000)
  k0 := (945316542180381/250000000000000000)
  k6 := (2949666855908209/250000000000000000)
  q := (164127998830181317727/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13469]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13469]

theorem width_13470 : mW 13470 = 283652480023581 := by
  have hu : mW 13470 ≤ 283652480023581 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13470 ≤ 283652480023580 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13470 : RowArithmetic 13470 (1141597400438562753937/1000000000000000000000000) (615585307835876220728737/1000000000000000000000000) (8088792806867311/1000000000000000000000000) where
  r0 := (159914783739/250000000000000000)
  k0 := (1890527814280089/500000000000000000)
  k6 := (5899114727287609/500000000000000000)
  q := (20516761440344331303/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13470]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13470]

theorem width_13471 : mW 13471 = 283726190180422 := by
  have hu : mW 13471 ≤ 283726190180422 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13471 ≤ 283726190180421 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13471 : RowArithmetic 13471 (11415616200913488041/10000000000000000000000) (615573021154178345506347/1000000000000000000000000) (8087227079942399/1000000000000000000000000) where
  r0 := (639587910037/1000000000000000000)
  k0 := (945211278938701/250000000000000000)
  k6 := (2359558306857299/200000000000000000)
  q := (32828036797834865349/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13471]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13471]

theorem width_13472 : mW 13472 = 283799914017947 := by
  have hu : mW 13472 ≤ 283799914017947 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13472 ≤ 283799914017946 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13472 : RowArithmetic 13472 (570762924326955376183/500000000000000000000000) (30778036815415468727343/50000000000000000000000) (50535386103499/6250000000000000000000) where
  r0 := (319758349167/500000000000000000)
  k0 := (756126926058447/200000000000000000)
  k6 := (737334603922351/62500000000000000)
  q := (164146276229465528501/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13472]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13472]

theorem width_13473 : mW 13473 = 283873651537679 := by
  have hu : mW 13473 ≤ 283873651537679 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13473 ≤ 283873651537678 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13473 : RowArithmetic 13473 (570745043061672588999/500000000000000000000000) (615548453297831278684151/1000000000000000000000000) (1010512112071573/125000000000000000000000) where
  r0 := (159861374961/250000000000000000)
  k0 := (3780424172168171/1000000000000000000)
  k6 := (11796915839979533/1000000000000000000)
  q := (16415236824365343283/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13473]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13473]

theorem width_13474 : mW 13474 = 283947402741142 := by
  have hu : mW 13474 ≤ 283947402741142 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13474 ≤ 283947402741141 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13474 : RowArithmetic 13474 (114145433249674913827/100000000000000000000000) (153884043030576556925701/250000000000000000000000) (8082532439833613/1000000000000000000000000) where
  r0 := (127874862913/200000000000000000)
  k0 := (3780213741381267/1000000000000000000)
  k6 := (5898239032971601/500000000000000000)
  q := (164158460031763212201/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13474]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13474]

theorem width_13475 : mW 13475 = 284021167629859 := by
  have hu : mW 13475 ≤ 284021167629859 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13475 ≤ 284021167629858 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13475 : RowArithmetic 13475 (228283717554244326477/200000000000000000000000) (615523892781296414294323/1000000000000000000000000) (8080968406196003/1000000000000000000000000) where
  r0 := (159825785623/250000000000000000)
  k0 := (756000667584261/200000000000000000)
  k6 := (5898020170319789/500000000000000000)
  q := (16416455159382003441/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13475]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13475]

theorem width_13476 : mW 13476 = 284094946205354 := by
  have hu : mW 13476 ≤ 284094946205354 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13476 ≤ 284094946205353 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13476 : RowArithmetic 13476 (285345712985965534221/250000000000000000000000) (307755807637182122367887/500000000000000000000000) (1615880959102573/200000000000000000000000) where
  r0 := (639231983623/1000000000000000000)
  k0 := (755958592357387/200000000000000000)
  k6 := (5897801332029811/500000000000000000)
  q := (82085321464924531293/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13476]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13476]

theorem width_13477 : mW 13477 = 284168738469150 := by
  have hu : mW 13477 ≤ 284168738469150 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13477 ≤ 284168738469149 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13477 : RowArithmetic 13477 (228269425002354413661/200000000000000000000000) (123099867920214455950333/200000000000000000000000) (8077841607637403/1000000000000000000000000) where
  r0 := (319580418977/500000000000000000)
  k0 := (236223913310681/62500000000000000)
  k6 := (5897582518097147/500000000000000000)
  q := (164176734039875455187/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13477]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13477]

theorem width_13478 : mW 13478 = 284242544422771 := by
  have hu : mW 13478 ≤ 284242544422771 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13478 ≤ 284242544422770 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13478 : RowArithmetic 13478 (570655703486026659929/500000000000000000000000) (615487065760983191546303/1000000000000000000000000) (4038139421211427/500000000000000000000000) where
  r0 := (15977242637/25000000000000000)
  k0 := (1889686145731481/500000000000000000)
  k6 := (5897363728517279/500000000000000000)
  q := (82091412461962183003/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13478]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13478]

theorem width_13479 : mW 13479 = 284316364067740 := by
  have hu : mW 13479 ≤ 284316364067740 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13479 ≤ 284316364067739 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13479 : RowArithmetic 13479 (285318924455452430703/250000000000000000000000) (615474793753659775494177/1000000000000000000000000) (8074716499722551/1000000000000000000000000) where
  r0 := (3195092931/5000000000000000)
  k0 := (1889580998632369/500000000000000000)
  k6 := (11794289926571381/1000000000000000000)
  q := (164188915582020944171/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13479]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13479]

theorem width_13480 : mW 13480 = 284390197405582 := by
  have hu : mW 13480 ≤ 284390197405582 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13480 ≤ 284390197405581 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13480 : RowArithmetic 13480 (1141239997558144854533/1000000000000000000000000) (615462523578665032126649/1000000000000000000000000) (8073154579389831/1000000000000000000000000) where
  r0 := (63894748011/100000000000000000)
  k0 := (3778951730368953/1000000000000000000)
  k6 := (2948463111198933/250000000000000000)
  q := (2565546968971723971/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13480]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13480]

theorem width_13481 : mW 13481 = 284464044437821 := by
  have hu : mW 13481 ≤ 284464044437821 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13481 ≤ 284464044437820 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13481 : RowArithmetic 13481 (1141204306178164229779/1000000000000000000000000) (307725127617781028210477/500000000000000000000000) (8071593081278123/1000000000000000000000000) where
  r0 := (127775277441/200000000000000000)
  k0 := (1889370745382689/500000000000000000)
  k6 := (589670750584929/50000000000000000)
  q := (82100548110228837863/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13481]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13481]

theorem width_13482 : mW 13482 = 284537905165979 := by
  have hu : mW 13482 ≤ 284537905165979 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13482 ≤ 284537905165978 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13482 : RowArithmetic 13482 (1141168623678976027757/1000000000000000000000000) (123087597744782826755243/200000000000000000000000) (8070032005240979/1000000000000000000000000) where
  r0 := (638805307483/1000000000000000000)
  k0 := (755706255690531/200000000000000000)
  k6 := (117929776272709/10000000000000000)
  q := (164207186200848104053/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13482]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13482]

theorem width_13483 : mW 13483 = 284611779591582 := by
  have hu : mW 13483 ≤ 284611779591582 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13483 ≤ 284611779591581 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13483 : RowArithmetic 13483 (570566475028843357261/500000000000000000000000) (615425724043284582322863/1000000000000000000000000) (4034235675565949/500000000000000000000000) where
  r0 := (31936712047/50000000000000000)
  k0 := (3778321093423507/1000000000000000000)
  k6 := (11792540291503667/1000000000000000000)
  q := (82106637977693374801/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13483]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13483]

theorem width_13484 : mW 13484 = 284685667716153 := by
  have hu : mW 13484 ≤ 284685667716153 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13484 ≤ 284685667716152 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13484 : RowArithmetic 13484 (1141097285311406149191/1000000000000000000000000) (76926682649154625756639/125000000000000000000000) (806691111880453/100000000000000000000000) where
  r0 := (319331593787/500000000000000000)
  k0 := (944527733919143/250000000000000000)
  k6 := (11792103004387859/1000000000000000000)
  q := (16421936548409873819/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13484]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13484]

theorem width_13485 : mW 13485 = 284759569541216 := by
  have hu : mW 13485 ≤ 284759569541216 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13485 ≤ 284759569541215 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13485 : RowArithmetic 13485 (570530814718622332613/500000000000000000000000) (615401200173335069898803/1000000000000000000000000) (100816891351407/12500000000000000000000) where
  r0 := (638592147379/1000000000000000000)
  k0 := (59029700081229/15625000000000000)
  k6 := (1473958220739307/125000000000000000)
  q := (164225454787009190977/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13485]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13485]

theorem width_13486 : mW 13486 = 284833485068295 := by
  have hu : mW 13486 ≤ 284833485068295 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13486 ≤ 284833485068294 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13486 : RowArithmetic 13486 (228205196486462759877/200000000000000000000000) (615388940983142574083519/1000000000000000000000000) (4031895959454867/500000000000000000000000) where
  r0 := (319260560177/500000000000000000)
  k0 := (3777690701991351/1000000000000000000)
  k6 := (294780714401861/25000000000000000)
  q := (10264471491508951529/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13486]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13486]

theorem width_13487 : mW 13487 = 284907414298915 := by
  have hu : mW 13487 ≤ 284907414298915 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13487 ≤ 284907414298914 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13487 : RowArithmetic 13487 (1140990344293725563361/1000000000000000000000000) (307688341811111757139323/500000000000000000000000) (8062232951049837/1000000000000000000000000) where
  r0 := (319225053247/500000000000000000)
  k0 := (755496125208883/200000000000000000)
  k6 := (5895395717429399/500000000000000000)
  q := (5132426022360185953/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13487]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13487]

theorem width_13488 : mW 13488 = 284981357234600 := by
  have hu : mW 13488 ≤ 284981357234600 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13488 ≤ 284981357234599 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13488 : RowArithmetic 13488 (1140954715018593899503/1000000000000000000000000) (307682214045070994239009/500000000000000000000000) (8060674404386743/1000000000000000000000000) where
  r0 := (638379105797/1000000000000000000)
  k0 := (11803970554239/3125000000000000)
  k6 := (2947588585564629/250000000000000000)
  q := (82121860670591238133/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13488]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13488]

theorem width_13489 : mW 13489 = 285055313876873 := by
  have hu : mW 13489 ≤ 285055313876873 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13489 ≤ 285055313876872 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13489 : RowArithmetic 13489 (285229773651008669647/250000000000000000000000) (153838043596615552636347/250000000000000000000000) (8059116278774419/1000000000000000000000000) where
  r0 := (319154059129/500000000000000000)
  k0 := (37770605559173/10000000000000000)
  k6 := (1473739662283073/125000000000000000)
  q := (164249809741137904309/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13489]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13489]

theorem width_13490 : mW 13490 = 285129284227260 := by
  have hu : mW 13490 ≤ 285129284227260 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13490 ≤ 285129284227259 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13490 : RowArithmetic 13490 (570441741523581395277/500000000000000000000000) (615339922510748624820533/1000000000000000000000000) (805755857406681/100000000000000000000000) where
  r0 := (319118571937/500000000000000000)
  k0 := (755370112344509/200000000000000000)
  k6 := (11789480302867993/1000000000000000000)
  q := (5132996809856791641/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13490]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13490]

theorem width_13491 : mW 13491 = 285203268287284 := by
  have hu : mW 13491 ≤ 285203268287284 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13491 ≤ 285203268287283 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13491 : RowArithmetic 13491 (228169576069019301453/200000000000000000000000) (615327672462565749143157/1000000000000000000000000) (805600129011801/100000000000000000000000) where
  r0 := (638166182643/1000000000000000000)
  k0 := (3776640594770841/1000000000000000000)
  k6 := (11789043356059739/1000000000000000000)
  q := (41065496466011463527/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13491]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13491]

theorem width_13492 : mW 13492 = 285277266058471 := by
  have hu : mW 13492 ≤ 285277266058471 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13492 ≤ 285277266058470 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13492 : RowArithmetic 13492 (57040614324747656017/50000000000000000000000) (153828856060369556637743/250000000000000000000000) (8054444426782091/1000000000000000000000000) where
  r0 := (249255951/390625000000000)
  k0 := (3776430655051937/1000000000000000000)
  k6 := (11788606457830817/1000000000000000000)
  q := (164268073587048557681/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13492]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13492]

theorem width_13493 : mW 13493 = 285351277542344 := by
  have hu : mW 13493 ≤ 285351277542344 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13493 ≤ 285351277542343 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13493 : RowArithmetic 13493 (285194175373463325037/250000000000000000000000) (61530317784705093597241/100000000000000000000000) (1006610997989159/125000000000000000000000) where
  r0 := (319012149811/500000000000000000)
  k0 := (3776220742561497/1000000000000000000)
  k6 := (11788169608172227/1000000000000000000)
  q := (2566783766944539487/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13493]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13493]

theorem width_13494 : mW 13494 = 285425302740428 := by
  have hu : mW 13494 ≤ 285425302740428 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13494 ≤ 285425302740427 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13494 : RowArithmetic 13494 (228148225067783492583/200000000000000000000000) (615290933278848783023371/1000000000000000000000000) (8051331961365781/1000000000000000000000000) where
  r0 := (318976688913/500000000000000000)
  k0 := (3776010857295183/1000000000000000000)
  k6 := (1178773280707497/100000000000000000)
  q := (32856049671255368371/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13494]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13494]

theorem width_13495 : mW 13495 = 285499341654248 := by
  have hu : mW 13495 ≤ 285499341654248 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13495 ≤ 285499341654247 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13495 : RowArithmetic 13495 (142588194753408402951/125000000000000000000000) (307639345268218433542491/500000000000000000000000) (2012444089748477/250000000000000000000000) where
  r0 := (39867654323/62500000000000000)
  k0 := (3775800999245697/1000000000000000000)
  k6 := (235745921090601/20000000000000000)
  q := (32857267080510515277/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13495]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13495]

theorem width_13496 : mW 13496 = 285573394285329 := by
  have hu : mW 13496 ≤ 285573394285329 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13496 ≤ 285573394285328 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13496 : RowArithmetic 13496 (285167499889006348823/250000000000000000000000) (307633224809690239154403/500000000000000000000000) (4024110588326003/500000000000000000000000) where
  r0 := (127562314729/200000000000000000)
  k0 := (1887795584204349/500000000000000000)
  k6 := (11786859350528473/1000000000000000000)
  q := (164292422223302800753/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13496]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13496]

theorem width_13497 : mW 13497 = 285647460635195 := by
  have hu : mW 13497 ≤ 285647460635195 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13497 ≤ 285647460635194 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13497 : RowArithmetic 13497 (1140634449922316713049/1000000000000000000000000) (307627105263622490098097/500000000000000000000000) (201166660354863/25000000000000000000000) where
  r0 := (637740691253/1000000000000000000)
  k0 := (1887690682388441/500000000000000000)
  k6 := (11786422695061247/1000000000000000000)
  q := (82149254409276290157/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13497]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13497]

theorem width_13498 : mW 13498 = 285721540705371 := by
  have hu : mW 13498 ≤ 285721540705371 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13498 ≤ 285721540705370 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13498 : RowArithmetic 13498 (35643715910102074477/31250000000000000000000) (615241973259595899580241/1000000000000000000000000) (804511207147593/100000000000000000000000) where
  r0 := (637669821989/1000000000000000000)
  k0 := (1887585794172953/500000000000000000)
  k6 := (5892993044059691/500000000000000000)
  q := (6572183807533079031/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13498]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13498]

theorem width_13499 : mW 13499 = 285795634497382 := by
  have hu : mW 13499 ≤ 285795634497382 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13499 ≤ 285795634497381 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13499 : RowArithmetic 13499 (114056337715600080849/100000000000000000000000) (615229737815998855322839/1000000000000000000000000) (4021779074175389/500000000000000000000000) where
  r0 := (637598965851/1000000000000000000)
  k0 := (235935114944649/62500000000000000)
  k6 := (2946387382423473/250000000000000000)
  q := (164310681332651043207/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13499]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13499]

theorem width_13500 : mW 13500 = 285869742012753 := by
  have hu : mW 13500 ≤ 285869742012753 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13500 ≤ 285869742012752 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13500 : RowArithmetic 13500 (2851319635044118967/2500000000000000000000) (24608700167840790733143/40000000000000000000000) (1005250580584209/125000000000000000000000) where
  r0 := (637528122833/1000000000000000000)
  k0 := (3774752117069087/1000000000000000000)
  k6 := (11785113019775793/1000000000000000000)
  q := (82158383625774917019/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13500]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13500]

theorem width_13501 : mW 13501 = 285943863253008 := by
  have hu : mW 13501 ≤ 285943863253008 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13501 ≤ 285943863253007 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13501 : RowArithmetic 13501 (1140492339705336234471/1000000000000000000000000) (307602636199612247945029/500000000000000000000000) (8040451560299307/1000000000000000000000000) where
  r0 := (637457292933/1000000000000000000)
  k0 := (30196339377669/8000000000000000)
  k6 := (117846765583561/10000000000000000)
  q := (32864570589009679011/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13501]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13501]

theorem width_13502 : mW 13502 = 286017998219673 := by
  have hu : mW 13502 ≤ 286017998219673 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13502 ≤ 286017998219672 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13502 : RowArithmetic 13502 (285114208554049003689/250000000000000000000000) (615193042425179194985527/1000000000000000000000000) (2009724723770597/250000000000000000000000) where
  r0 := (159346619037/250000000000000000)
  k0 := (3774332754528647/1000000000000000000)
  k6 := (2946060036356459/250000000000000000)
  q := (41082234603292942103/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13502]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13502]

theorem width_13503 : mW 13503 = 286092146914273 := by
  have hu : mW 13503 ≤ 286092146914273 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13503 ≤ 286092146914272 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13503 : RowArithmetic 13503 (570210668773679054227/500000000000000000000000) (153795203568362510512243/250000000000000000000000) (803734664887771/100000000000000000000000) where
  r0 := (318657836237/500000000000000000)
  k0 := (3774123114021839/1000000000000000000)
  k6 := (11783803780976021/1000000000000000000)
  q := (82167511827972495811/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13503]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13503]

theorem width_13504 : mW 13504 = 286166309338333 := by
  have hu : mW 13504 ≤ 286166309338333 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13504 ≤ 286166309338332 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13504 : RowArithmetic 13504 (570192924847977444659/500000000000000000000000) (615168587943603437002667/1000000000000000000000000) (8035794821540131/1000000000000000000000000) where
  r0 := (637244881907/1000000000000000000)
  k0 := (754782700136177/200000000000000000)
  k6 := (5891683732498841/500000000000000000)
  q := (32868221734678619513/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13504]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13504]

theorem width_13505 : mW 13505 = 286240485493378 := by
  have hu : mW 13505 ≤ 286240485493378 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13505 ≤ 286240485493377 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13505 : RowArithmetic 13505 (570175185329559961711/500000000000000000000000) (615156363435205908237891/1000000000000000000000000) (2008560853231143/250000000000000000000000) where
  r0 := (127434820889/200000000000000000)
  k0 := (377370391450439/100000000000000000)
  k6 := (11782931197481843/1000000000000000000)
  q := (32869438693108222897/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13505]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13505]

theorem width_13506 : mW 13506 = 286314675380934 := by
  have hu : mW 13506 ≤ 286314675380934 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13506 ≤ 286314675380933 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13506 : RowArithmetic 13506 (1140314900433987246757/1000000000000000000000000) (15378603518695602629149/25000000000000000000000) (8032692422885989/1000000000000000000000000) where
  r0 := (159275835021/250000000000000000)
  k0 := (3773494355485033/1000000000000000000)
  k6 := (736405936151221/62500000000000000)
  q := (32870655606482813199/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13506]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13506]

theorem width_13507 : mW 13507 = 286388879002525 := by
  have hu : mW 13507 ≤ 286388879002525 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13507 ≤ 286388879002524 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13507 : RowArithmetic 13507 (570139719508846765247/500000000000000000000000) (307565959940512419164079/500000000000000000000000) (8031141851279457/1000000000000000000000000) where
  r0 := (31851629441/50000000000000000)
  k0 := (3773284823615493/1000000000000000000)
  k6 := (11782058807801791/1000000000000000000)
  q := (82179681187018485537/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13507]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13507]

theorem width_13508 : mW 13508 = 286463096359677 := by
  have hu : mW 13508 ≤ 286463096359677 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13508 ≤ 286463096359676 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13508 : RowArithmetic 13508 (228048797281475038537/200000000000000000000000) (615119700834375040722097/1000000000000000000000000) (8029591697960057/1000000000000000000000000) where
  r0 := (12739237013/20000000000000000)
  k0 := (235817207430713/62500000000000000)
  k6 := (5890811342809821/500000000000000000)
  q := (20545680811304355509/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13508]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13508]

theorem width_13509 : mW 13509 = 286537327453916 := by
  have hu : mW 13509 ≤ 286537327453916 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13509 ≤ 286537327453915 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13509 : RowArithmetic 13509 (1140208542600169842389/1000000000000000000000000) (76888435450930225297569/125000000000000000000000) (1605608392556587/200000000000000000000000) where
  r0 := (636891125571/1000000000000000000)
  k0 := (754573168261683/200000000000000000)
  k6 := (5890593305932063/500000000000000000)
  q := (164371530381632694709/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13509]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13509]

theorem width_13510 : mW 13510 = 286611572286766 := by
  have hu : mW 13510 ≤ 286611572286766 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13510 ≤ 286611572286765 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13510 : RowArithmetic 13510 (570086553796608860027/500000000000000000000000) (615095268199792336614819/1000000000000000000000000) (1003311580700419/125000000000000000000000) where
  r0 := (636820413579/1000000000000000000)
  k0 := (754531278171837/200000000000000000)
  k6 := (11780750586526281/1000000000000000000)
  q := (6575104561906221123/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13510]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13510]

theorem width_13511 : mW 13511 = 286685830859754 := by
  have hu : mW 13511 ≤ 286685830859754 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13511 ≤ 286685830859753 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13511 : RowArithmetic 13511 (228027536276731618553/200000000000000000000000) (615083054610994013926751/1000000000000000000000000) (1003117968284569/125000000000000000000000) where
  r0 := (636749714671/1000000000000000000)
  k0 := (471555870942419/125000000000000000)
  k6 := (2945078652399287/250000000000000000)
  q := (164383697488528344637/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13511]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13511]

theorem width_13512 : mW 13512 = 286760103174405 := by
  have hu : mW 13512 ≤ 286760103174405 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13512 ≤ 286760103174404 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13512 : RowArithmetic 13512 (28502556599215821443/25000000000000000000000) (615070842840614329942119/1000000000000000000000000) (1604679052931579/200000000000000000000000) where
  r0 := (159169757211/250000000000000000)
  k0 := (3772237571344547/1000000000000000000)
  k6 := (11779878681067771/1000000000000000000)
  q := (164389780704276140233/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13512]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13512]

theorem width_13513 : mW 13513 = 286834389232245 := by
  have hu : mW 13513 ≤ 286834389232245 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13513 ≤ 286834389232244 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13513 : RowArithmetic 13513 (570033427672642189873/500000000000000000000000) (615058632888220952780359/1000000000000000000000000) (1002730900075347/125000000000000000000000) where
  r0 := (636608356093/1000000000000000000)
  k0 := (3772028202264473/1000000000000000000)
  k6 := (5889721400464597/500000000000000000)
  q := (41098965923730976519/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13513]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13513]

theorem width_13514 : mW 13514 = 286908689034798 := by
  have hu : mW 13514 ≤ 286908689034798 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13514 ≤ 286908689034797 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13514 : RowArithmetic 13514 (1140031455510757650019/1000000000000000000000000) (307523212376690830884163/500000000000000000000000) (802029955396671/100000000000000000000000) where
  r0 := (636537696417/1000000000000000000)
  k0 := (942954715075171/250000000000000000)
  k6 := (11779006969172467/1000000000000000000)
  q := (164401946460496628757/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13514]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13514]

theorem width_13515 : mW 13515 = 286983002583593 := by
  have hu : mW 13515 ≤ 286983002583593 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13515 ≤ 286983002583592 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13515 : RowArithmetic 13515 (569998032231097624809/500000000000000000000000) (615034218435664386567419/1000000000000000000000000) (2004688081151283/250000000000000000000000) where
  r0 := (636467049811/1000000000000000000)
  k0 := (3771609545442881/1000000000000000000)
  k6 := (5889285592894319/500000000000000000)
  q := (32881605800203858049/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13515]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13515]

theorem width_13516 : mW 13516 = 287057329880152 := by
  have hu : mW 13516 ≤ 287057329880152 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13516 ≤ 287057329880151 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13516 : RowArithmetic 13516 (1139960682196745980421/1000000000000000000000000) (615022013934637177004227/1000000000000000000000000) (400860275618687/50000000000000000000000) where
  r0 := (636396416271/1000000000000000000)
  k0 := (3771400257683723/1000000000000000000)
  k6 := (294453386269219/25000000000000000)
  q := (82207055658258433943/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13516]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13516]

theorem width_13517 : mW 13517 = 287131670926004 := by
  have hu : mW 13517 ≤ 287131670926004 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13517 ≤ 287131670926003 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13517 : RowArithmetic 13517 (1139925308711554796881/1000000000000000000000000) (30750490562493412537457/50000000000000000000000) (8015659117128093/1000000000000000000000000) where
  r0 := (159081448949/250000000000000000)
  k0 := (94279774925619/25000000000000000)
  k6 := (11777699764103889/1000000000000000000)
  q := (164420193407014334409/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13517]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13517]

theorem width_13518 : mW 13518 = 287206025722674 := by
  have hu : mW 13518 ≤ 287206025722674 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13518 ≤ 287206025722673 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13518 : RowArithmetic 13518 (22797798880075414291/20000000000000000000000) (153749402595231501174083/250000000000000000000000) (801411313872393/100000000000000000000000) where
  r0 := (31812759419/50000000000000000)
  k0 := (1885490881726361/500000000000000000)
  k6 := (11777264125785081/1000000000000000000)
  q := (164426275272536657921/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13518]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13518]

theorem width_13519 : mW 13519 = 287280394271687 := by
  have hu : mW 13519 ≤ 287280394271687 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13519 ≤ 287280394271686 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13519 : RowArithmetic 13519 (1139854588070543932371/1000000000000000000000000) (307492705663689421545359/500000000000000000000000) (1001570947127131/125000000000000000000000) where
  r0 := (318092297011/500000000000000000)
  k0 := (942693139242289/250000000000000000)
  k6 := (2944207133950849/250000000000000000)
  q := (32886471382621760383/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13519]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13519]

theorem width_13520 : mW 13520 = 287354776574569 := by
  have hu : mW 13520 ≤ 287354776574569 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13520 ≤ 287354776574568 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13520 : RowArithmetic 13520 (569909620454512557319/500000000000000000000000) (307486607044397722171123/500000000000000000000000) (8011022431863281/1000000000000000000000000) where
  r0 := (636114012717/1000000000000000000)
  k0 := (3016450702051/800000000000000)
  k6 := (2355278598829979/200000000000000000)
  q := (10277402395547232829/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13520]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13520]

theorem width_13521 : mW 13521 = 287429172632848 := by
  have hu : mW 13521 ≤ 287429172632848 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13521 ≤ 287429172632847 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13521 : RowArithmetic 13521 (284945975629091168701/250000000000000000000000) (307480509332372312331429/500000000000000000000000) (8009477703118469/1000000000000000000000000) where
  r0 := (318021722231/500000000000000000)
  k0 := (3770354225232121/1000000000000000000)
  k6 := (11775957500815643/1000000000000000000)
  q := (16444451951950238223/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13521]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13521]

theorem width_13522 : mW 13522 = 287503582448048 := by
  have hu : mW 13522 ≤ 287503582448048 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13522 ≤ 287503582448047 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13522 : RowArithmetic 13522 (1139748572889717078687/1000000000000000000000000) (614948825054795213786371/1000000000000000000000000) (8007933390638627/1000000000000000000000000) where
  r0 := (635972889253/1000000000000000000)
  k0 := (3770145099966917/1000000000000000000)
  k6 := (5887761027895853/500000000000000000)
  q := (164450600485373722457/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13522]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13522]

theorem width_13523 : mW 13523 = 287578006021697 := by
  have hu : mW 13523 ≤ 287578006021697 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13523 ≤ 287578006021696 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13523 : RowArithmetic 13523 (1139713252026235105799/1000000000000000000000000) (614936633258516282120599/1000000000000000000000000) (8006389494279719/1000000000000000000000000) where
  r0 := (39743896693/62500000000000000)
  k0 := (753987200353343/200000000000000000)
  k6 := (11775086659069153/1000000000000000000)
  q := (164456681226394690979/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13523]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13523]

theorem width_13524 : mW 13524 = 287652443355320 := by
  have hu : mW 13524 ≤ 287652443355320 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13524 ≤ 287652443355319 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13524 : RowArithmetic 13524 (1139677939923074868099/1000000000000000000000000) (122984888655095413987573/200000000000000000000000) (62537859483577/7812500000000000000000) where
  r0 := (635831817963/1000000000000000000)
  k0 := (23560793316401/6250000000000000)
  k6 := (5887325655319527/500000000000000000)
  q := (82231380871295114109/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13524]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13524]

theorem width_13525 : mW 13525 = 287726894450443 := by
  have hu : mW 13525 ≤ 287726894450443 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13525 ≤ 287726894450442 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13525 : RowArithmetic 13525 (1139642636577392941273/1000000000000000000000000) (122982451021049372477291/200000000000000000000000) (8003302949349183/1000000000000000000000000) where
  r0 := (1017218083/1600000000000000)
  k0 := (1884758943267431/500000000000000000)
  k6 := (2943554002623121/250000000000000000)
  q := (32893768406797053997/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13525]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13525]

theorem width_13526 : mW 13526 = 287801359308594 := by
  have hu : mW 13526 ≤ 287801359308594 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13526 ≤ 287801359308593 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13526 : RowArithmetic 13526 (142450917748293206261/125000000000000000000000) (122980013749479032026959/200000000000000000000000) (2000440075122463/250000000000000000000000) where
  r0 := (635690798819/1000000000000000000)
  k0 := (3769308869488497/1000000000000000000)
  k6 := (11773780758620517/1000000000000000000)
  q := (164474922100604747483/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13526]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13526]

theorem width_13527 : mW 13527 = 287875837931298 := by
  have hu : mW 13527 ≤ 287875837931298 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13527 ≤ 287875837931297 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13527 : RowArithmetic 13527 (1139572056147092647083/1000000000000000000000000) (76860985525186451576549/125000000000000000000000) (4000109033588081/500000000000000000000000) where
  r0 := (317810154397/500000000000000000)
  k0 := (18845499397433/5000000000000000)
  k6 := (11773345555014231/1000000000000000000)
  q := (32896200388494717461/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13527]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13527]

theorem width_13528 : mW 13528 = 287950330320082 := by
  have hu : mW 13528 ≤ 287950330320082 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13528 ≤ 287950330320081 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13528 : RowArithmetic 13528 (113953677905679333261/100000000000000000000000) (614875701467105866662441/1000000000000000000000000) (1599735249852883/200000000000000000000000) where
  r0 := (127109966359/200000000000000000)
  k0 := (942222729129711/250000000000000000)
  k6 := (2943227599916177/250000000000000000)
  q := (164487081559616711439/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13528]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13528]

theorem width_13529 : mW 13529 = 288024836476473 := by
  have hu : mW 13529 ≤ 288024836476473 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13529 ≤ 288024836476472 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13529 : RowArithmetic 13529 (1139501510712608286553/1000000000000000000000000) (122972704108761580036893/200000000000000000000000) (399856742330549/50000000000000000000000) where
  r0 := (635479367819/1000000000000000000)
  k0 := (3768681980580831/1000000000000000000)
  k6 := (2943118823140757/250000000000000000)
  q := (164493160952059037269/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13529]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13529]

theorem width_13530 : mW 13530 = 288099356401997 := by
  have hu : mW 13530 ≤ 288099356401997 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13530 ≤ 288099356401996 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13530 : RowArithmetic 13530 (569733125555849991007/500000000000000000000000) (307425670715583851124689/500000000000000000000000) (7995593859072311/1000000000000000000000000) where
  r0 := (317704458431/500000000000000000)
  k0 := (1884236535832597/500000000000000000)
  k6 := (5886020116850139/500000000000000000)
  q := (16449924011982547757/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13530]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13530]

theorem width_13531 : mW 13531 = 288173890098180 := by
  have hu : mW 13531 ≤ 288173890098180 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13531 ≤ 288173890098179 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13531 : RowArithmetic 13531 (1139431000251232069129/1000000000000000000000000) (30741958206437774281457/50000000000000000000000) (7994053286504929/1000000000000000000000000) where
  r0 := (317669239461/500000000000000000)
  k0 := (3768264189770497/1000000000000000000)
  k6 := (2354321044613509/200000000000000000)
  q := (82252659531470470259/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13531]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13531]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 13457 then ⟨(285515839266318220917/250000000000000000000000), (615745201957948150932959/1000000000000000000000000), (8109185866272983/1000000000000000000000000)⟩ else
  if n = 13458 then ⟨(114202746062620118519/100000000000000000000000), (615732891370547773100539/1000000000000000000000000), (1013451827485783/125000000000000000000000)⟩ else
  if n = 13459 then ⟨(1141991573134760988387/1000000000000000000000000), (307860291312341920175563/500000000000000000000000), (2026510949739859/250000000000000000000000)⟩ else
  if n = 13460 then ⟨(1141955694588032348237/1000000000000000000000000), (12314165514398328552227/20000000000000000000000), (8104473403344587/1000000000000000000000000)⟩ else
  if n = 13461 then ⟨(57095991249154863763/50000000000000000000000), (4810124770748482900029/7812500000000000000000), (8102903432893893/1000000000000000000000000)⟩ else
  if n = 13462 then ⟨(142735495539629966657/125000000000000000000000), (307841833715956164163869/500000000000000000000000), (4050666943729813/500000000000000000000000)⟩ else
  if n = 13463 then ⟨(1141848112586944901761/1000000000000000000000000), (615671366047796565137587/1000000000000000000000000), (4049882383447061/500000000000000000000000)⟩ else
  if n = 13464 then ⟨(570906134894948485213/500000000000000000000000), (307829533251509569435093/500000000000000000000000), (8098196071049693/1000000000000000000000000)⟩ else
  if n = 13465 then ⟨(1141776435922983551151/1000000000000000000000000), (12312935375942818271003/20000000000000000000000), (4048313899889403/500000000000000000000000)⟩ else
  if n = 13466 then ⟨(228348122196658693921/200000000000000000000000), (153908618232430709975259/250000000000000000000000), (4047529976466993/500000000000000000000000)⟩ else
  if n = 13467 then ⟨(228340958993583059301/200000000000000000000000), (307811089450163000827149/500000000000000000000000), (809349253036777/100000000000000000000000)⟩ else
  if n = 13468 then ⟨(114166898787393955129/100000000000000000000000), (615609886708511673168899/1000000000000000000000000), (1618385106386557/200000000000000000000000)⟩ else
  if n = 13469 then ⟨(570816594849228616541/500000000000000000000000), (615597596353841239861843/1000000000000000000000000), (4045179478740847/500000000000000000000000)⟩ else
  if n = 13470 then ⟨(1141597400438562753937/1000000000000000000000000), (615585307835876220728737/1000000000000000000000000), (8088792806867311/1000000000000000000000000)⟩ else
  if n = 13471 then ⟨(11415616200913488041/10000000000000000000000), (615573021154178345506347/1000000000000000000000000), (8087227079942399/1000000000000000000000000)⟩ else
  if n = 13472 then ⟨(570762924326955376183/500000000000000000000000), (30778036815415468727343/50000000000000000000000), (50535386103499/6250000000000000000000)⟩ else
  if n = 13473 then ⟨(570745043061672588999/500000000000000000000000), (615548453297831278684151/1000000000000000000000000), (1010512112071573/125000000000000000000000)⟩ else
  if n = 13474 then ⟨(114145433249674913827/100000000000000000000000), (153884043030576556925701/250000000000000000000000), (8082532439833613/1000000000000000000000000)⟩ else
  if n = 13475 then ⟨(228283717554244326477/200000000000000000000000), (615523892781296414294323/1000000000000000000000000), (8080968406196003/1000000000000000000000000)⟩ else
  if n = 13476 then ⟨(285345712985965534221/250000000000000000000000), (307755807637182122367887/500000000000000000000000), (1615880959102573/200000000000000000000000)⟩ else
  if n = 13477 then ⟨(228269425002354413661/200000000000000000000000), (123099867920214455950333/200000000000000000000000), (8077841607637403/1000000000000000000000000)⟩ else
  if n = 13478 then ⟨(570655703486026659929/500000000000000000000000), (615487065760983191546303/1000000000000000000000000), (4038139421211427/500000000000000000000000)⟩ else
  if n = 13479 then ⟨(285318924455452430703/250000000000000000000000), (615474793753659775494177/1000000000000000000000000), (8074716499722551/1000000000000000000000000)⟩ else
  if n = 13480 then ⟨(1141239997558144854533/1000000000000000000000000), (615462523578665032126649/1000000000000000000000000), (8073154579389831/1000000000000000000000000)⟩ else
  if n = 13481 then ⟨(1141204306178164229779/1000000000000000000000000), (307725127617781028210477/500000000000000000000000), (8071593081278123/1000000000000000000000000)⟩ else
  if n = 13482 then ⟨(1141168623678976027757/1000000000000000000000000), (123087597744782826755243/200000000000000000000000), (8070032005240979/1000000000000000000000000)⟩ else
  if n = 13483 then ⟨(570566475028843357261/500000000000000000000000), (615425724043284582322863/1000000000000000000000000), (4034235675565949/500000000000000000000000)⟩ else
  if n = 13484 then ⟨(1141097285311406149191/1000000000000000000000000), (76926682649154625756639/125000000000000000000000), (806691111880453/100000000000000000000000)⟩ else
  if n = 13485 then ⟨(570530814718622332613/500000000000000000000000), (615401200173335069898803/1000000000000000000000000), (100816891351407/12500000000000000000000)⟩ else
  if n = 13486 then ⟨(228205196486462759877/200000000000000000000000), (615388940983142574083519/1000000000000000000000000), (4031895959454867/500000000000000000000000)⟩ else
  if n = 13487 then ⟨(1140990344293725563361/1000000000000000000000000), (307688341811111757139323/500000000000000000000000), (8062232951049837/1000000000000000000000000)⟩ else
  if n = 13488 then ⟨(1140954715018593899503/1000000000000000000000000), (307682214045070994239009/500000000000000000000000), (8060674404386743/1000000000000000000000000)⟩ else
  if n = 13489 then ⟨(285229773651008669647/250000000000000000000000), (153838043596615552636347/250000000000000000000000), (8059116278774419/1000000000000000000000000)⟩ else
  if n = 13490 then ⟨(570441741523581395277/500000000000000000000000), (615339922510748624820533/1000000000000000000000000), (805755857406681/100000000000000000000000)⟩ else
  if n = 13491 then ⟨(228169576069019301453/200000000000000000000000), (615327672462565749143157/1000000000000000000000000), (805600129011801/100000000000000000000000)⟩ else
  if n = 13492 then ⟨(57040614324747656017/50000000000000000000000), (153828856060369556637743/250000000000000000000000), (8054444426782091/1000000000000000000000000)⟩ else
  if n = 13493 then ⟨(285194175373463325037/250000000000000000000000), (61530317784705093597241/100000000000000000000000), (1006610997989159/125000000000000000000000)⟩ else
  if n = 13494 then ⟨(228148225067783492583/200000000000000000000000), (615290933278848783023371/1000000000000000000000000), (8051331961365781/1000000000000000000000000)⟩ else
  if n = 13495 then ⟨(142588194753408402951/125000000000000000000000), (307639345268218433542491/500000000000000000000000), (2012444089748477/250000000000000000000000)⟩ else
  if n = 13496 then ⟨(285167499889006348823/250000000000000000000000), (307633224809690239154403/500000000000000000000000), (4024110588326003/500000000000000000000000)⟩ else
  if n = 13497 then ⟨(1140634449922316713049/1000000000000000000000000), (307627105263622490098097/500000000000000000000000), (201166660354863/25000000000000000000000)⟩ else
  if n = 13498 then ⟨(35643715910102074477/31250000000000000000000), (615241973259595899580241/1000000000000000000000000), (804511207147593/100000000000000000000000)⟩ else
  if n = 13499 then ⟨(114056337715600080849/100000000000000000000000), (615229737815998855322839/1000000000000000000000000), (4021779074175389/500000000000000000000000)⟩ else
  if n = 13500 then ⟨(2851319635044118967/2500000000000000000000), (24608700167840790733143/40000000000000000000000), (1005250580584209/125000000000000000000000)⟩ else
  if n = 13501 then ⟨(1140492339705336234471/1000000000000000000000000), (307602636199612247945029/500000000000000000000000), (8040451560299307/1000000000000000000000000)⟩ else
  if n = 13502 then ⟨(285114208554049003689/250000000000000000000000), (615193042425179194985527/1000000000000000000000000), (2009724723770597/250000000000000000000000)⟩ else
  if n = 13503 then ⟨(570210668773679054227/500000000000000000000000), (153795203568362510512243/250000000000000000000000), (803734664887771/100000000000000000000000)⟩ else
  if n = 13504 then ⟨(570192924847977444659/500000000000000000000000), (615168587943603437002667/1000000000000000000000000), (8035794821540131/1000000000000000000000000)⟩ else
  if n = 13505 then ⟨(570175185329559961711/500000000000000000000000), (615156363435205908237891/1000000000000000000000000), (2008560853231143/250000000000000000000000)⟩ else
  if n = 13506 then ⟨(1140314900433987246757/1000000000000000000000000), (15378603518695602629149/25000000000000000000000), (8032692422885989/1000000000000000000000000)⟩ else
  if n = 13507 then ⟨(570139719508846765247/500000000000000000000000), (307565959940512419164079/500000000000000000000000), (8031141851279457/1000000000000000000000000)⟩ else
  if n = 13508 then ⟨(228048797281475038537/200000000000000000000000), (615119700834375040722097/1000000000000000000000000), (8029591697960057/1000000000000000000000000)⟩ else
  if n = 13509 then ⟨(1140208542600169842389/1000000000000000000000000), (76888435450930225297569/125000000000000000000000), (1605608392556587/200000000000000000000000)⟩ else
  if n = 13510 then ⟨(570086553796608860027/500000000000000000000000), (615095268199792336614819/1000000000000000000000000), (1003311580700419/125000000000000000000000)⟩ else
  if n = 13511 then ⟨(228027536276731618553/200000000000000000000000), (615083054610994013926751/1000000000000000000000000), (1003117968284569/125000000000000000000000)⟩ else
  if n = 13512 then ⟨(28502556599215821443/25000000000000000000000), (615070842840614329942119/1000000000000000000000000), (1604679052931579/200000000000000000000000)⟩ else
  if n = 13513 then ⟨(570033427672642189873/500000000000000000000000), (615058632888220952780359/1000000000000000000000000), (1002730900075347/125000000000000000000000)⟩ else
  if n = 13514 then ⟨(1140031455510757650019/1000000000000000000000000), (307523212376690830884163/500000000000000000000000), (802029955396671/100000000000000000000000)⟩ else
  if n = 13515 then ⟨(569998032231097624809/500000000000000000000000), (615034218435664386567419/1000000000000000000000000), (2004688081151283/250000000000000000000000)⟩ else
  if n = 13516 then ⟨(1139960682196745980421/1000000000000000000000000), (615022013934637177004227/1000000000000000000000000), (400860275618687/50000000000000000000000)⟩ else
  if n = 13517 then ⟨(1139925308711554796881/1000000000000000000000000), (30750490562493412537457/50000000000000000000000), (8015659117128093/1000000000000000000000000)⟩ else
  if n = 13518 then ⟨(22797798880075414291/20000000000000000000000), (153749402595231501174083/250000000000000000000000), (801411313872393/100000000000000000000000)⟩ else
  if n = 13519 then ⟨(1139854588070543932371/1000000000000000000000000), (307492705663689421545359/500000000000000000000000), (1001570947127131/125000000000000000000000)⟩ else
  if n = 13520 then ⟨(569909620454512557319/500000000000000000000000), (307486607044397722171123/500000000000000000000000), (8011022431863281/1000000000000000000000000)⟩ else
  if n = 13521 then ⟨(284945975629091168701/250000000000000000000000), (307480509332372312331429/500000000000000000000000), (8009477703118469/1000000000000000000000000)⟩ else
  if n = 13522 then ⟨(1139748572889717078687/1000000000000000000000000), (614948825054795213786371/1000000000000000000000000), (8007933390638627/1000000000000000000000000)⟩ else
  if n = 13523 then ⟨(1139713252026235105799/1000000000000000000000000), (614936633258516282120599/1000000000000000000000000), (8006389494279719/1000000000000000000000000)⟩ else
  if n = 13524 then ⟨(1139677939923074868099/1000000000000000000000000), (122984888655095413987573/200000000000000000000000), (62537859483577/7812500000000000000000)⟩ else
  if n = 13525 then ⟨(1139642636577392941273/1000000000000000000000000), (122982451021049372477291/200000000000000000000000), (8003302949349183/1000000000000000000000000)⟩ else
  if n = 13526 then ⟨(142450917748293206261/125000000000000000000000), (122980013749479032026959/200000000000000000000000), (2000440075122463/250000000000000000000000)⟩ else
  if n = 13527 then ⟨(1139572056147092647083/1000000000000000000000000), (76860985525186451576549/125000000000000000000000), (4000109033588081/500000000000000000000000)⟩ else
  if n = 13528 then ⟨(113953677905679333261/100000000000000000000000), (614875701467105866662441/1000000000000000000000000), (1599735249852883/200000000000000000000000)⟩ else
  if n = 13529 then ⟨(1139501510712608286553/1000000000000000000000000), (122972704108761580036893/200000000000000000000000), (399856742330549/50000000000000000000000)⟩ else
  if n = 13530 then ⟨(569733125555849991007/500000000000000000000000), (307425670715583851124689/500000000000000000000000), (7995593859072311/1000000000000000000000000)⟩ else
  ⟨(1139431000251232069129/1000000000000000000000000), (30741958206437774281457/50000000000000000000000), (7994053286504929/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 13457 ≤ n) (hb : n ≤ 13531) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_13457
  · exact row_13458
  · exact row_13459
  · exact row_13460
  · exact row_13461
  · exact row_13462
  · exact row_13463
  · exact row_13464
  · exact row_13465
  · exact row_13466
  · exact row_13467
  · exact row_13468
  · exact row_13469
  · exact row_13470
  · exact row_13471
  · exact row_13472
  · exact row_13473
  · exact row_13474
  · exact row_13475
  · exact row_13476
  · exact row_13477
  · exact row_13478
  · exact row_13479
  · exact row_13480
  · exact row_13481
  · exact row_13482
  · exact row_13483
  · exact row_13484
  · exact row_13485
  · exact row_13486
  · exact row_13487
  · exact row_13488
  · exact row_13489
  · exact row_13490
  · exact row_13491
  · exact row_13492
  · exact row_13493
  · exact row_13494
  · exact row_13495
  · exact row_13496
  · exact row_13497
  · exact row_13498
  · exact row_13499
  · exact row_13500
  · exact row_13501
  · exact row_13502
  · exact row_13503
  · exact row_13504
  · exact row_13505
  · exact row_13506
  · exact row_13507
  · exact row_13508
  · exact row_13509
  · exact row_13510
  · exact row_13511
  · exact row_13512
  · exact row_13513
  · exact row_13514
  · exact row_13515
  · exact row_13516
  · exact row_13517
  · exact row_13518
  · exact row_13519
  · exact row_13520
  · exact row_13521
  · exact row_13522
  · exact row_13523
  · exact row_13524
  · exact row_13525
  · exact row_13526
  · exact row_13527
  · exact row_13528
  · exact row_13529
  · exact row_13530
  · exact row_13531

end BstLean.Part271.R3.Rows13457
