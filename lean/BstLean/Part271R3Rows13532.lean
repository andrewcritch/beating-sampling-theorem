import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 13532–13606. -/
namespace BstLean.Part271.R3.Rows13532
open Real BstLean.Part130 BstLean.Part227

theorem width_13532 : mW 13532 = 288248437566550 := by
  have hu : mW 13532 ≤ 288248437566550 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13532 ≤ 288248437566549 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13532 : RowArithmetic 13532 (1139395758128367947023/1000000000000000000000000) (61482698863614156137523/100000000000000000000000) (7992513128765357/1000000000000000000000000) where
  r0 := (127053610799/200000000000000000)
  k0 := (942013833722343/250000000000000000)
  k6 := (11771170260655917/1000000000000000000)
  q := (82255698890715164843/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13532]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13532]

theorem width_13533 : mW 13533 = 288322998808633 := by
  have hu : mW 13533 ≤ 288322998808633 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13533 ≤ 288322998808632 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13533 : RowArithmetic 13533 (284840131185068404963/250000000000000000000000) (307407407476448157783389/500000000000000000000000) (7990973385710239/1000000000000000000000000) where
  r0 := (317598821039/500000000000000000)
  k0 := (3767846507017411/1000000000000000000)
  k6 := (11770735346456487/1000000000000000000)
  q := (41129369068829636011/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13533]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13533]

theorem width_13534 : mW 13534 = 288397573825957 := by
  have hu : mW 13534 ≤ 288397573825957 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13534 ≤ 288397573825956 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13534 : RowArithmetic 13534 (1139325300084114840733/1000000000000000000000000) (61480264307859040216759/100000000000000000000000) (7989434057196223/1000000000000000000000000) where
  r0 := (635127243167/1000000000000000000)
  k0 := (1883818853073621/500000000000000000)
  k6 := (11770300480460349/1000000000000000000)
  q := (164523554544630477967/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13534]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13534]

theorem width_13535 : mW 13535 = 288472162620047 := by
  have hu : mW 13535 ≤ 288472162620047 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13535 ≤ 288472162620046 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13535 : RowArithmetic 13535 (284822521039265169527/250000000000000000000000) (614790473012794526324453/1000000000000000000000000) (1597579028616021/200000000000000000000000) where
  r0 := (635056857259/1000000000000000000)
  k0 := (3767428932274457/1000000000000000000)
  k6 := (11769865662658599/1000000000000000000)
  q := (82264816294695510613/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13535]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13535]

theorem width_13536 : mW 13536 = 288546765192431 := by
  have hu : mW 13536 ≤ 288546765192431 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13536 ≤ 288546765192430 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13536 : RowArithmetic 13536 (1139254876956279235641/1000000000000000000000000) (614778304755079583178079/1000000000000000000000000) (3993178321609329/500000000000000000000000) where
  r0 := (12699729687/20000000000000000)
  k0 := (3767220185391677/1000000000000000000)
  k6 := (2353886178608467/200000000000000000)
  q := (164535710409625058999/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13536]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13536]

theorem width_13537 : mW 13537 = 288621381544636 := by
  have hu : mW 13537 ≤ 288621381544636 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13537 ≤ 288621381544635 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13537 : RowArithmetic 13537 (569609839239470252439/500000000000000000000000) (614766138305016597248189/1000000000000000000000000) (998102319683593/125000000000000000000000) where
  r0 := (317458062219/500000000000000000)
  k0 := (1883505732748729/500000000000000000)
  k6 := (588449808580133/50000000000000000)
  q := (82270894002678735933/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13537]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13537]

theorem width_13538 : mW 13538 = 288696011678189 := by
  have hu : mW 13538 ≤ 288696011678189 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13538 ≤ 288696011678188 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13538 : RowArithmetic 13538 (56959224436110782561/50000000000000000000000) (614753973662176653390043/1000000000000000000000000) (997910110710911/125000000000000000000000) where
  r0 := (317422888759/500000000000000000)
  k0 := (3766802772581451/1000000000000000000)
  k6 := (470742459933227/40000000000000000)
  q := (82273932688306567907/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13538]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13538]

theorem width_13539 : mW 13539 = 288770655594617 := by
  have hu : mW 13539 ≤ 288770655594617 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13539 ≤ 288770655594616 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13539 : RowArithmetic 13539 (569574653841638506647/500000000000000000000000) (153685452706532770921337/250000000000000000000000) (3990871813865639/500000000000000000000000) where
  r0 := (158693860897/250000000000000000)
  k0 := (3766594106642207/1000000000000000000)
  k6 := (11768126873217487/1000000000000000000)
  q := (82276971261708461117/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13539]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13539]

theorem width_13540 : mW 13540 = 288845313295447 := by
  have hu : mW 13540 ≤ 288845313295447 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13540 ≤ 288845313295446 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13540 : RowArithmetic 13540 (284778533839824525581/250000000000000000000000) (76841206224556414130457/125000000000000000000000) (3990103391728881/500000000000000000000000) where
  r0 := (634705122643/1000000000000000000)
  k0 := (6026216748271/1600000000000000)
  k6 := (2941923074063551/250000000000000000)
  q := (82280009722896848963/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13540]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13540]

theorem width_13541 : mW 13541 = 288919984782206 := by
  have hu : mW 13541 ≤ 288919984782206 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13541 ≤ 288919984782205 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13541 : RowArithmetic 13541 (227815794349490720301/200000000000000000000000) (614717490572708904567887/1000000000000000000000000) (159573407054477/20000000000000000000000) where
  r0 := (317317407341/500000000000000000)
  k0 := (3766176855664469/1000000000000000000)
  k6 := (45965850654031/3906250000000000)
  q := (164566096143768325097/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13541]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13541]

theorem width_13542 : mW 13542 = 288994670056422 := by
  have hu : mW 13542 ≤ 288994670056422 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13542 ≤ 288994670056421 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13542 : RowArithmetic 13542 (284760954211229663683/250000000000000000000000) (307352666577237782010149/500000000000000000000000) (7977134335386687/1000000000000000000000000) where
  r0 := (6345645197/10000000000000000)
  k0 := (1882984135308567/500000000000000000)
  k6 := (5883411643370897/500000000000000000)
  q := (20571521577170707671/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13542]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13542]

theorem width_13543 : mW 13543 = 289069369119622 := by
  have hu : mW 13543 ≤ 289069369119622 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13543 ≤ 289069369119621 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13543 : RowArithmetic 13543 (1139008670648870288177/1000000000000000000000000) (614693177541323158701643/1000000000000000000000000) (3987799365651753/500000000000000000000000) where
  r0 := (317247118847/500000000000000000)
  k0 := (1882879856261473/500000000000000000)
  k6 := (2353277770834979/200000000000000000)
  q := (82289124433305279883/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13543]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13543]

theorem width_13544 : mW 13544 = 289144081973334 := by
  have hu : mW 13544 ≤ 289144081973334 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13544 ≤ 289144081973333 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13544 : RowArithmetic 13544 (1138973533156485988071/1000000000000000000000000) (614681023732823669873207/1000000000000000000000000) (7974063540331577/1000000000000000000000000) where
  r0 := (31721198433/50000000000000000)
  k0 := (753110236274903/200000000000000000)
  k6 := (2353190893944471/200000000000000000)
  q := (82292162445763934367/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13544]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13544]

theorem width_13545 : mW 13545 = 289218808619084 := by
  have hu : mW 13545 ≤ 289218808619084 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13545 ≤ 289218808619083 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13545 : RowArithmetic 13545 (569469202182472915387/500000000000000000000000) (307334435864274597691897/500000000000000000000000) (1993132190582071/250000000000000000000000) where
  r0 := (158588428149/250000000000000000)
  k0 := (188267133858519/50000000000000000)
  k6 := (11765520133375293/1000000000000000000)
  q := (82295200346071216063/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13545]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13545]

theorem width_13546 : mW 13546 = 289293549058400 := by
  have hu : mW 13546 ≤ 289293549058400 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13546 ≤ 289293549058399 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13546 : RowArithmetic 13546 (569451642135714820713/500000000000000000000000) (61465672152807200546337/100000000000000000000000) (3985497198575509/500000000000000000000000) where
  r0 := (317141734749/500000000000000000)
  k0 := (1882567099951573/500000000000000000)
  k6 := (11765085845124831/1000000000000000000)
  q := (41149119067119772303/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13546]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13546]

theorem width_13547 : mW 13547 = 289368303292811 := by
  have hu : mW 13547 ≤ 289368303292811 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13547 ≤ 289368303292810 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13547 : RowArithmetic 13547 (1138868172873117705491/1000000000000000000000000) (38415285820685282092523/62500000000000000000000) (1593892088931441/200000000000000000000000) where
  r0 := (317106619681/500000000000000000)
  k0 := (752985149913083/200000000000000000)
  k6 := (5882325802481047/500000000000000000)
  q := (164602551620562674679/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13547]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13547]

theorem width_13548 : mW 13548 = 289443071323843 := by
  have hu : mW 13548 ≤ 289443071323843 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13548 ≤ 289443071323842 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13548 : RowArithmetic 13548 (1138833070167193604877/1000000000000000000000000) (307316213268399643098777/500000000000000000000000) (1593585380940883/200000000000000000000000) where
  r0 := (317071511093/500000000000000000)
  k0 := (941179331538931/250000000000000000)
  k6 := (5882108706439103/500000000000000000)
  q := (41152156687104504657/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13548]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13548]

theorem width_13549 : mW 13549 = 289517853153024 := by
  have hu : mW 13549 ≤ 289517853153024 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13549 ≤ 289517853153023 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13549 : RowArithmetic 13549 (142349747018855083779/125000000000000000000000) (1229240563490297909649/2000000000000000000000) (318655751086009/40000000000000000000000) where
  r0 := (317036408983/500000000000000000)
  k0 := (3764508929666671/1000000000000000000)
  k6 := (5881891634432149/500000000000000000)
  q := (164614701652069946581/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13549]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13549]

theorem width_13550 : mW 13550 = 289592648781882 := by
  have hu : mW 13550 ≤ 289592648781882 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13550 ≤ 289592648781881 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13550 : RowArithmetic 13550 (1138762890821243399757/1000000000000000000000000) (614608138755586363421179/1000000000000000000000000) (497803816365767/62500000000000000000000) where
  r0 := (317001313349/500000000000000000)
  k0 := (941075140022713/250000000000000000)
  k6 := (11763349172911499/1000000000000000000)
  q := (164620776331543279477/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13550]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13550]

theorem width_13551 : mW 13551 = 289667458211944 := by
  have hu : mW 13551 ≤ 289667458211944 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13551 ≤ 289667458211943 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13551 : RowArithmetic 13551 (1138727814175588166481/1000000000000000000000000) (153648999391921110217743/250000000000000000000000) (7963328758668283/1000000000000000000000000) where
  r0 := (633932448379/1000000000000000000)
  k0 := (3764092217423831/1000000000000000000)
  k6 := (11762915125010943/1000000000000000000)
  q := (82313425393431416839/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13551]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13551]

theorem width_13552 : mW 13552 = 289742281444740 := by
  have hu : mW 13552 ≤ 289742281444740 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13552 ≤ 289742281444739 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13552 : RowArithmetic 13552 (1138692746211060385757/1000000000000000000000000) (122916771636203262241051/200000000000000000000000) (1990449216863991/250000000000000000000000) where
  r0 := (633862283007/1000000000000000000)
  k0 := (1881941950832069/500000000000000000)
  k6 := (5881240562576883/500000000000000000)
  q := (82316462509026710483/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13552]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13552]

theorem width_13553 : mW 13553 = 289817118481795 := by
  have hu : mW 13553 ≤ 289817118481795 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13553 ≤ 289817118481794 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13553 : RowArithmetic 13553 (1138657686924850177473/1000000000000000000000000) (76821465074394403109767/125000000000000000000000) (398013269403661/50000000000000000000000) where
  r0 := (633792130577/1000000000000000000)
  k0 := (752735122560279/200000000000000000)
  k6 := (367563974166597/31250000000000000)
  q := (164638999025139848547/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13553]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13553]

theorem width_13554 : mW 13554 = 289891969324639 := by
  have hu : mW 13554 ≤ 289891969324639 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13554 ≤ 289891969324638 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13554 : RowArithmetic 13554 (1138622636314145288031/1000000000000000000000000) (614559584809674539694039/1000000000000000000000000) (198968358009447/25000000000000000000000) where
  r0 := (316860995543/500000000000000000)
  k0 := (3763467350831159/1000000000000000000)
  k6 := (5880806634767049/500000000000000000)
  q := (3292901456162938381/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13554]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13554]

theorem width_13555 : mW 13555 = 289966833974799 := by
  have hu : mW 13555 ≤ 289966833974799 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13555 ≤ 289966833974798 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13555 : RowArithmetic 13555 (142323449297017093841/125000000000000000000000) (614547450824147763626039/1000000000000000000000000) (7957203664227917/1000000000000000000000000) where
  r0 := (633651864531/1000000000000000000)
  k0 := (940814778937247/250000000000000000)
  k6 := (11761179413753891/1000000000000000000)
  q := (16465114636709943053/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13555]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13555]

theorem width_13556 : mW 13556 = 290041712433804 := by
  have hu : mW 13556 ≤ 290041712433804 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13556 ≤ 290041712433803 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13556 : RowArithmetic 13556 (569276280554007674359/500000000000000000000000) (4916282549105188228147/8000000000000000000000) (7955673419481309/1000000000000000000000000) where
  r0 := (158395437727/250000000000000000)
  k0 := (1881525453773733/500000000000000000)
  k6 := (5880372802990813/500000000000000000)
  q := (164657219702022176469/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13556]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13556]

theorem width_13557 : mW 13557 = 290116604703181 := by
  have hu : mW 13557 ≤ 290116604703181 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13557 ≤ 290116604703180 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13557 : RowArithmetic 13557 (569258768253487220847/500000000000000000000000) (122904637650250128540161/200000000000000000000000) (994267948249519/125000000000000000000000) where
  r0 := (126702330043/200000000000000000)
  k0 := (752568545245023/200000000000000000)
  k6 := (11760311846208451/1000000000000000000)
  q := (6586531712517597831/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13557]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13557]

theorem width_13558 : mW 13558 = 290191510784459 := by
  have hu : mW 13558 ≤ 290191510784459 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13558 ≤ 290191510784458 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13558 : RowArithmetic 13558 (1138482520570207139181/1000000000000000000000000) (38406941228939252488257/62500000000000000000000) (1988153540907637/250000000000000000000000) where
  r0 := (633441562447/1000000000000000000)
  k0 := (3762634571771547/1000000000000000000)
  k6 := (2351975626885103/200000000000000000)
  q := (164669365699877522787/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13558]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13558]

theorem width_13559 : mW 13559 = 290266430679165 := by
  have hu : mW 13559 ≤ 290266430679165 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13559 ≤ 290266430679164 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13559 : RowArithmetic 13559 (1138447513294909124783/1000000000000000000000000) (307249466436527381057257/500000000000000000000000) (3975542576121357/500000000000000000000000) where
  r0 := (316685743801/500000000000000000)
  k0 := (1881213222092641/500000000000000000)
  k6 := (11759444470623969/1000000000000000000)
  q := (164675438362859687273/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13559]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13559]

theorem width_13560 : mW 13560 = 290341364388829 := by
  have hu : mW 13560 ≤ 290341364388829 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13560 ≤ 290341364388828 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13560 : RowArithmetic 13560 (1138412514678275126749/1000000000000000000000000) (2400339093284785394983/3906250000000000000000) (248423642240339/31250000000000000000000) where
  r0 := (158325356419/250000000000000000)
  k0 := (3762218343458897/1000000000000000000)
  k6 := (11759010854794967/1000000000000000000)
  q := (5146297212559725451/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13560]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13560]

theorem width_13561 : mW 13561 = 290416311914979 := by
  have hu : mW 13561 ≤ 290416311914979 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13561 ≤ 290416311914978 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13561 : RowArithmetic 13561 (1138377524717502446169/1000000000000000000000000) (122894936937230647301881/200000000000000000000000) (7948028361833263/1000000000000000000000000) where
  r0 := (316615688333/500000000000000000)
  k0 := (3762010269587937/1000000000000000000)
  k6 := (2351715457385933/200000000000000000)
  q := (32937516603411374979/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13561]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13561]

theorem width_13562 : mW 13562 = 290491273259142 := by
  have hu : mW 13562 ≤ 290491273259142 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13562 ≤ 290491273259141 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13562 : RowArithmetic 13562 (284585635852447562191/250000000000000000000000) (614462563288373752573073/1000000000000000000000000) (7946500582528359/1000000000000000000000000) where
  r0 := (79145167571/125000000000000000)
  k0 := (3761802222564977/1000000000000000000)
  k6 := (11758143767019221/1000000000000000000)
  q := (164693655008321434727/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13562]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13562]

theorem width_13563 : mW 13563 = 290566248422848 := by
  have hu : mW 13563 ≤ 290566248422848 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13563 ≤ 290566248422847 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13563 : RowArithmetic 13563 (284576892688084186443/250000000000000000000000) (122890088737428250737331/200000000000000000000000) (3972486606817259/500000000000000000000000) where
  r0 := (31654565869/50000000000000000)
  k0 := (376159420238853/100000000000000000)
  k6 := (2351542059010959/200000000000000000)
  q := (164699726775729655429/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13563]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13563]

theorem width_13564 : mW 13564 = 290641237407625 := by
  have hu : mW 13564 ≤ 290641237407625 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13564 ≤ 290641237407624 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13564 : RowArithmetic 13564 (227654521348468543517/200000000000000000000000) (61443832588203052051893/100000000000000000000000) (1985861563752559/250000000000000000000000) where
  r0 := (633021307097/1000000000000000000)
  k0 := (752277241809639/200000000000000000)
  k6 := (367414902219611/31250000000000000)
  q := (10294112394956643371/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13564]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13564]

theorem width_13565 : mW 13565 = 290716240215001 := by
  have hu : mW 13565 ≤ 290716240215001 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13565 ≤ 290716240215000 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13565 : RowArithmetic 13565 (569118825688505051411/500000000000000000000000) (614426209872616386283897/1000000000000000000000000) (794191970651407/100000000000000000000000) where
  r0 := (632951309717/1000000000000000000)
  k0 := (1880589121271241/500000000000000000)
  k6 := (2351368698985731/200000000000000000)
  q := (164711869639076102621/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13565]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13565]

theorem width_13566 : mW 13566 = 290791256846506 := by
  have hu : mW 13566 ≤ 290791256846506 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13566 ≤ 290791256846505 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13566 : RowArithmetic 13566 (1138202704653540591033/1000000000000000000000000) (614414095658473937717119/1000000000000000000000000) (1588078713600917/200000000000000000000000) where
  r0 := (158220331309/250000000000000000)
  k0 := (3760970302863957/1000000000000000000)
  k6 := (1469551270843659/125000000000000000)
  q := (32943588147012765859/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13566]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13566]

theorem width_13567 : mW 13567 = 290866287303667 := by
  have hu : mW 13567 ≤ 290866287303667 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13567 ≤ 290866287303666 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13567 : RowArithmetic 13567 (1138167766569139140283/1000000000000000000000000) (614401983239178279864061/1000000000000000000000000) (3969433919670243/500000000000000000000000) where
  r0 := (632811353651/1000000000000000000)
  k0 := (752152478001631/200000000000000000)
  k6 := (5877988443240287/500000000000000000)
  q := (20590501450911777151/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13567]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13567]

theorem width_13568 : mW 13568 = 290941331588014 := by
  have hu : mW 13568 ≤ 290941331588014 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13568 ≤ 290941331588013 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13568 : RowArithmetic 13568 (1138132837121009755597/1000000000000000000000000) (122877974522860959561823/200000000000000000000000) (7937342520380461/1000000000000000000000000) where
  r0 := (632741394959/1000000000000000000)
  k0 := (940138625992653/250000000000000000)
  k6 := (1175554365411373/100000000000000000)
  q := (164730082255792005053/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13568]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13568]

theorem width_13569 : mW 13569 = 291016389701075 := by
  have hu : mW 13569 ≤ 291016389701075 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13569 ≤ 291016389701074 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13569 : RowArithmetic 13569 (569048958153179502517/500000000000000000000000) (614377763783428874077051/1000000000000000000000000) (793581761098331/100000000000000000000000) where
  r0 := (126534289831/200000000000000000)
  k0 := (752069328948183/200000000000000000)
  k6 := (11755110469639917/1000000000000000000)
  q := (82368076340290963481/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13569]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13569]

theorem width_13570 : mW 13570 = 291091461644379 := by
  have hu : mW 13570 ≤ 291091461644379 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13570 ≤ 291091461644378 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13570 : RowArithmetic 13570 (569031502061196954829/500000000000000000000000) (153591414186531532582383/250000000000000000000000) (1983573277751967/250000000000000000000000) where
  r0 := (316300758119/500000000000000000)
  k0 := (1880069406160269/500000000000000000)
  k6 := (11754677333050311/1000000000000000000)
  q := (164742222881688712511/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13570]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13570]

theorem width_13571 : mW 13571 = 291166547419455 := by
  have hu : mW 13571 ≤ 291166547419455 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13571 ≤ 291166547419454 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13571 : RowArithmetic 13571 (71126756285395165391/62500000000000000000000) (614353551501972247297603/1000000000000000000000000) (7932769020313033/1000000000000000000000000) where
  r0 := (632531596203/1000000000000000000)
  k0 := (1879965503349533/500000000000000000)
  k6 := (11754244244336089/1000000000000000000)
  q := (128709603796200849/781250000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13571]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13571]

theorem width_13572 : mW 13572 = 291241647027833 := by
  have hu : mW 13572 ≤ 291241647027833 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13572 ≤ 291241647027832 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13572 : RowArithmetic 13572 (568996602817676922599/500000000000000000000000) (614341448050543117843803/1000000000000000000000000) (7931245338757733/1000000000000000000000000) where
  r0 := (632461689047/1000000000000000000)
  k0 := (3759723227872027/1000000000000000000)
  k6 := (5876905601744217/500000000000000000)
  q := (32950872522590354011/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13572]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13572]

theorem width_13573 : mW 13573 = 291316760471040 := by
  have hu : mW 13573 ≤ 291316760471040 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13573 ≤ 291316760471039 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13573 : RowArithmetic 13573 (284489579831674849057/250000000000000000000000) (307164673195707373884467/500000000000000000000000) (99121525827513/12500000000000000000000) where
  r0 := (39524487173/62500000000000000)
  k0 := (1879757737918959/500000000000000000)
  k6 := (11753378210498529/1000000000000000000)
  q := (41190108035789369607/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13573]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13573]

theorem width_13574 : mW 13574 = 291391887750607 := by
  have hu : mW 13574 ≤ 291391887750607 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13574 ≤ 291391887750606 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13574 : RowArithmetic 13574 (568961720818784768427/500000000000000000000000) (614317246524163217059133/1000000000000000000000000) (7928199202501979/1000000000000000000000000) where
  r0 := (7904023917/12500000000000000)
  k0 := (234956734411459/62500000000000000)
  k6 := (11752945265357559/1000000000000000000)
  q := (82383250724889461599/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13574]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13574]

theorem width_13575 : mW 13575 = 291467028868062 := by
  have hu : mW 13575 ≤ 291467028868062 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13575 ≤ 291467028868061 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13575 : RowArithmetic 13575 (1137888572565177762123/1000000000000000000000000) (76788143556045601484679/125000000000000000000000) (7926676747519717/1000000000000000000000000) where
  r0 := (316126022411/500000000000000000)
  k0 := (1879550026054887/500000000000000000)
  k6 := (1469064046007089/125000000000000000)
  q := (6590902821313632447/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13575]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13575]

theorem width_13576 : mW 13576 = 291542183824935 := by
  have hu : mW 13576 ≤ 291542183824935 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13576 ≤ 291542183824934 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13576 : RowArithmetic 13576 (1137853712106737317873/1000000000000000000000000) (614293052163595973932057/1000000000000000000000000) (3962577350556713/500000000000000000000000) where
  r0 := (12643643783/20000000000000000)
  k0 := (1879446190204877/500000000000000000)
  k6 := (5876039759293589/500000000000000000)
  q := (20597329924045980577/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13576]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13576]

theorem width_13577 : mW 13577 = 291617352622754 := by
  have hu : mW 13577 ≤ 291617352622754 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13577 ≤ 291617352622753 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13577 : RowArithmetic 13577 (1137818860259464003219/1000000000000000000000000) (122856191533886651773189/200000000000000000000000) (1584726612628479/200000000000000000000000) where
  r0 := (632112346341/1000000000000000000)
  k0 := (1879342367739401/500000000000000000)
  k6 := (235032934338803/20000000000000000)
  q := (164784708028384721231/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13577]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13577]

theorem width_13578 : mW 13578 = 291692535263049 := by
  have hu : mW 13578 ≤ 291692535263049 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13578 ≤ 291692535263048 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13578 : RowArithmetic 13578 (1137784017020573368039/1000000000000000000000000) (307134432482726621179629/500000000000000000000000) (3961055916732959/500000000000000000000000) where
  r0 := (632042516391/1000000000000000000)
  k0 := (3758477117309463/1000000000000000000)
  k6 := (11751213963106823/1000000000000000000)
  q := (164790776440916134183/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13578]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13578]

theorem width_13579 : mW 13579 = 291767731747350 := by
  have hu : mW 13579 ≤ 291767731747350 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13579 ≤ 291767731747349 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13579 : RowArithmetic 13579 (1137749182387282114211/1000000000000000000000000) (614256774051232822494577/1000000000000000000000000) (7920591011943349/1000000000000000000000000) where
  r0 := (631972699297/1000000000000000000)
  k0 := (939567381474313/250000000000000000)
  k6 := (11750781257078393/1000000000000000000)
  q := (164796844629986772087/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13579]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13579]

theorem width_13580 : mW 13580 = 291842942077185 := by
  have hu : mW 13580 ≤ 291842942077185 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13580 ≤ 291842942077184 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13580 : RowArithmetic 13580 (1137714356356809493239/1000000000000000000000000) (614244684926348993707237/1000000000000000000000000) (98988382480427/12500000000000000000000) where
  r0 := (39493930941/62500000000000000)
  k0 := (3758061961237681/1000000000000000000)
  k6 := (11750348598846059/1000000000000000000)
  q := (164802912595621319013/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13580]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13580]

theorem width_13581 : mW 13581 = 291918166254085 := by
  have hu : mW 13581 ≤ 291918166254085 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13581 ≤ 291918166254084 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13581 : RowArithmetic 13581 (1137679538926373808533/1000000000000000000000000) (614232597590378740329221/1000000000000000000000000) (3958775296398899/500000000000000000000000) where
  r0 := (39489568979/62500000000000000)
  k0 := (469731802915411/125000000000000000)
  k6 := (91796218659383/7812500000000000)
  q := (164808980337844454489/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13581]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13581]

theorem width_13582 : mW 13582 = 291993404279579 := by
  have hu : mW 13582 ≤ 291993404279579 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13582 ≤ 291993404279578 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13582 : RowArithmetic 13582 (1137644730093195911897/1000000000000000000000000) (614220512042899380149791/1000000000000000000000000) (7916030994893829/1000000000000000000000000) where
  r0 := (315881662559/500000000000000000)
  k0 := (234852932009349/62500000000000000)
  k6 := (1174948342573449/100000000000000000)
  q := (164815047856680853497/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13582]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13582]

theorem width_13583 : mW 13583 = 292068656155195 := by
  have hu : mW 13583 ≤ 292068656155195 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13583 ≤ 292068656155194 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13583 : RowArithmetic 13583 (1137609929854498501703/1000000000000000000000000) (122841685656697650214913/200000000000000000000000) (494656987786369/62500000000000000000000) where
  r0 := (126338711883/200000000000000000)
  k0 := (939359856928019/250000000000000000)
  k6 := (2349810182167533/200000000000000000)
  q := (164821115152155186479/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13583]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13583]

theorem width_13584 : mW 13584 = 292143921882465 := by
  have hu : mW 13584 ≤ 292143921882465 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13584 ≤ 292143921882464 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13584 : RowArithmetic 13584 (568787569103751315581/500000000000000000000000) (4913570770493782765091/8000000000000000000000) (7912993021721627/1000000000000000000000000) where
  r0 := (631623806551/1000000000000000000)
  k0 := (3757231970003297/1000000000000000000)
  k6 := (2349723688740351/200000000000000000)
  q := (20603397778036514917/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13584]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13584]

theorem width_13585 : mW 13585 = 292219201462918 := by
  have hu : mW 13585 ≤ 292219201462918 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13585 ≤ 292219201462917 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13585 : RowArithmetic 13585 (227508071029886519413/200000000000000000000000) (614184266127180799287267/1000000000000000000000000) (7911474646172743/1000000000000000000000000) where
  r0 := (631554066523/1000000000000000000)
  k0 := (601123926243/160000000000000)
  k6 := (11748186024317973/1000000000000000000)
  q := (164833249073116313429/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13585]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13585]

theorem width_13586 : mW 13586 = 292294494898083 := by
  have hu : mW 13586 ≤ 292294494898083 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13586 ≤ 292294494898082 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13586 : RowArithmetic 13586 (1137505580677513842707/1000000000000000000000000) (614172187729439897799491/1000000000000000000000000) (7909956677795059/1000000000000000000000000) where
  r0 := (631484339329/1000000000000000000)
  k0 := (751363426951383/200000000000000000)
  k6 := (1174775365267753/100000000000000000)
  q := (82419657849326212791/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13586]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13586]

theorem width_13587 : mW 13587 = 292369802189491 := by
  have hu : mW 13587 ≤ 292369802189491 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13587 ≤ 292369802189490 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13587 : RowArithmetic 13587 (1137470814788971563227/1000000000000000000000000) (61416011111807807704683/100000000000000000000000) (3954219558224193/500000000000000000000000) where
  r0 := (157853656241/250000000000000000)
  k0 := (1878304878603671/500000000000000000)
  k6 := (5873660664385821/500000000000000000)
  q := (164845382100925108081/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13587]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13587]

theorem width_13588 : mW 13588 = 292445123338670 := by
  have hu : mW 13588 ≤ 292445123338670 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13588 ≤ 292445123338669 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13588 : RowArithmetic 13588 (4443109599535289811/3906250000000000000000) (614148036292673377471883/1000000000000000000000000) (7906921961992679/1000000000000000000000000) where
  r0 := (25253796937/40000000000000000)
  k0 := (3756402406365531/1000000000000000000)
  k6 := (469875562103661/40000000000000000)
  q := (41212862069989752169/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13588]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13588]

theorem width_13589 : mW 13589 = 292520458347152 := by
  have hu : mW 13589 ≤ 292520458347152 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13589 ≤ 292520458347151 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13589 : RowArithmetic 13589 (113740130875092851863/100000000000000000000000) (122827192650560793117627/200000000000000000000000) (1976351303571961/250000000000000000000000) where
  r0 := (631275234709/1000000000000000000)
  k0 := (3756195082226981/1000000000000000000)
  k6 := (11746456824128401/1000000000000000000)
  q := (164857514235778770583/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13589]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13589]

theorem width_13590 : mW 13590 = 292595807216465 := by
  have hu : mW 13590 ≤ 292595807216465 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13590 ≤ 292595807216464 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13590 : RowArithmetic 13590 (1137366568595885267183/1000000000000000000000000) (30706194599902406801313/50000000000000000000000) (1580777774638791/200000000000000000000000) where
  r0 := (157801389703/250000000000000000)
  k0 := (3755987784784211/1000000000000000000)
  k6 := (1174602464337349/100000000000000000)
  q := (41215894992102258121/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13590]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13590]

theorem width_13591 : mW 13591 = 292671169948141 := by
  have hu : mW 13591 ≤ 292671169948141 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13591 ≤ 292671169948140 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13591 : RowArithmetic 13591 (113733183701313351913/100000000000000000000000) (614111822527984399046641/1000000000000000000000000) (7902372938571039/1000000000000000000000000) where
  r0 := (157783973933/250000000000000000)
  k0 := (938945128508923/250000000000000000)
  k6 := (183524882973719/15625000000000000)
  q := (164869645477874428527/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13591]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13591]

theorem width_13592 : mW 13592 = 292746546543709 := by
  have hu : mW 13592 ≤ 292746546543709 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13592 ≤ 292746546543708 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13592 : RowArithmetic 13592 (142162139249988198667/125000000000000000000000) (122819950968438272830297/200000000000000000000000) (246901794071227/31250000000000000000000) where
  r0 := (126213249093/200000000000000000)
  k0 := (187778663498697/50000000000000000)
  k6 := (11745160424953207/1000000000000000000)
  q := (164875710764199588333/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13592]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13592]

theorem width_13593 : mW 13593 = 292821937004699 := by
  have hu : mW 13593 ≤ 292821937004699 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13593 ≤ 292821937004698 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13593 : RowArithmetic 13593 (1137262399553434239663/1000000000000000000000000) (614087688940247709597191/1000000000000000000000000) (493708893011177/62500000000000000000000) where
  r0 := (630996608007/1000000000000000000)
  k0 := (234710378286967/62500000000000000)
  k6 := (11744728387270291/1000000000000000000)
  q := (41220443956852284247/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13593]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13593]

theorem width_13594 : mW 13594 = 292897341332642 := by
  have hu : mW 13594 ≤ 292897341332642 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13594 ≤ 292897341332641 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13594 : RowArithmetic 13594 (1137227693670952679857/1000000000000000000000000) (61407562482173234071967/100000000000000000000000) (7897827572129977/1000000000000000000000000) where
  r0 := (630926983357/1000000000000000000)
  k0 := (58674357217027/15625000000000000)
  k6 := (5872148198630249/500000000000000000)
  q := (41221960166881923763/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13594]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13594]

theorem width_13595 : mW 13595 = 292972759529068 := by
  have hu : mW 13595 ≤ 292972759529068 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13595 ≤ 292972759529067 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13595 : RowArithmetic 13595 (1137192996349695957691/1000000000000000000000000) (614063562486224259999069/1000000000000000000000000) (7896313261993021/1000000000000000000000000) where
  r0 := (630857371509/1000000000000000000)
  k0 := (3754951697855267/1000000000000000000)
  k6 := (5871932227457531/500000000000000000)
  q := (41223476321144969639/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13595]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13595]

theorem width_13596 : mW 13596 = 293048191595506 := by
  have hu : mW 13596 ≤ 293048191595506 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13596 ≤ 293048191595505 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13596 : RowArithmetic 13596 (284289576896725239219/250000000000000000000000) (1918910943541570569581/3125000000000000000000) (1973699839407093/250000000000000000000000) where
  r0 := (630787772461/1000000000000000000)
  k0 := (469343070060819/125000000000000000)
  k6 := (5871716280112609/500000000000000000)
  q := (82449984839295149503/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13596]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13596]

theorem width_13597 : mW 13597 = 293123637533488 := by
  have hu : mW 13597 ≤ 293123637533488 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13597 ≤ 293123637533487 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13597 : RowArithmetic 13597 (1137123627379803618793/1000000000000000000000000) (307019721581273298746499/500000000000000000000000) (7893285858896419/1000000000000000000000000) where
  r0 := (630718186209/1000000000000000000)
  k0 := (3754537449776091/1000000000000000000)
  k6 := (2935750178295551/250000000000000000)
  q := (164906033849583563381/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13597]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13597]

theorem width_13598 : mW 13598 = 293199097344544 := by
  have hu : mW 13598 ≤ 293199097344544 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13598 ≤ 293199097344543 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13598 : RowArithmetic 13598 (35534029866426325471/31250000000000000000000) (614027386173535725647759/1000000000000000000000000) (1578354553131533/200000000000000000000000) where
  r0 := (630648612751/1000000000000000000)
  k0 := (1877165182861171/500000000000000000)
  k6 := (11742568913777261/1000000000000000000)
  q := (20614012224698034267/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13598]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13598]

theorem width_13599 : mW 13599 = 293274571030205 := by
  have hu : mW 13599 ≤ 293274571030205 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13599 ≤ 293274571030204 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13599 : RowArithmetic 13599 (227410858524331252733/200000000000000000000000) (19187979092682797858849/31250000000000000000000) (7890260077772643/1000000000000000000000000) where
  r0 := (630579052083/1000000000000000000)
  k0 := (3754123308317809/1000000000000000000)
  k6 := (11742137162001629/1000000000000000000)
  q := (164918161522617029203/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13599]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13599]

theorem width_13600 : mW 13600 = 293350058592000 := by
  have hu : mW 13600 ≤ 293350058592000 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13600 ≤ 293350058591999 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13600 : RowArithmetic 13600 (1137019638065086609173/1000000000000000000000000) (15350081938476691064939/25000000000000000000000) (1972186948775501/250000000000000000000000) where
  r0 := (630509504201/1000000000000000000)
  k0 := (750783255510999/200000000000000000)
  k6 := (11741705457846553/1000000000000000000)
  q := (164924225024706421993/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13600]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13600]

theorem width_13601 : mW 13601 = 293425560031461 := by
  have hu : mW 13601 ≤ 293425560031461 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13601 ≤ 293425560031460 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13601 : RowArithmetic 13601 (284246248013293488753/250000000000000000000000) (306995612946384972164563/500000000000000000000000) (985904489688297/125000000000000000000000) where
  r0 := (630439969103/1000000000000000000)
  k0 := (1876854636716177/500000000000000000)
  k6 := (11741273801303281/1000000000000000000)
  q := (32986057660775408279/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13601]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13601]

theorem width_13602 : mW 13602 = 293501075350118 := by
  have hu : mW 13602 ≤ 293501075350118 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13602 ≤ 293501075350117 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13602 : RowArithmetic 13602 (1136950354583161330029/1000000000000000000000000) (4911833408212290711337/8000000000000000000000) (7885724444846501/1000000000000000000000000) where
  r0 := (9849538231/15625000000000000)
  k0 := (234593893496213/62500000000000000)
  k6 := (5870421096181531/500000000000000000)
  q := (164936351360153471779/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13602]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13602]

theorem width_13603 : mW 13603 = 293576604549502 := by
  have hu : mW 13603 ≤ 293576604549502 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13603 ≤ 293576604549501 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13603 : RowArithmetic 13603 (1136915725652292208157/1000000000000000000000000) (306983563969973493146753/500000000000000000000000) (3942106688491577/500000000000000000000000) where
  r0 := (630300937243/1000000000000000000)
  k0 := (3753295345077583/1000000000000000000)
  k6 := (2348082126203429/200000000000000000)
  q := (41235603548390073249/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13603]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13603]

theorem width_13604 : mW 13604 = 293652147631143 := by
  have hu : mW 13604 ≤ 293652147631143 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13604 ≤ 293652147631142 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13604 : RowArithmetic 13604 (568440552628905946607/500000000000000000000000) (306977540816290998168991/500000000000000000000000) (3941351356888599/500000000000000000000000) where
  r0 := (25209257619/40000000000000000)
  k0 := (3753088420836399/1000000000000000000)
  k6 := (5869989558628393/500000000000000000)
  q := (164948476804122080381/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13604]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13604]

theorem width_13605 : mW 13605 = 293727704596573 := by
  have hu : mW 13605 ≤ 293727704596573 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13605 ≤ 293727704596572 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13605 : RowArithmetic 13605 (1136846493396965441817/1000000000000000000000000) (61394303710402186871283/100000000000000000000000) (15762384910179/2000000000000000000000) where
  r0 := (630161956477/1000000000000000000)
  k0 := (150115260928453/40000000000000000)
  k6 := (11739547651073239/1000000000000000000)
  q := (164954539191863404751/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13605]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13605]

theorem width_13606 : mW 13606 = 293803275447322 := by
  have hu : mW 13606 ≤ 293803275447322 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13606 ≤ 293803275447321 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13606 : RowArithmetic 13606 (56840594503350021561/50000000000000000000000) (153482748588461753627431/250000000000000000000000) (3939841300390521/500000000000000000000000) where
  r0 := (315046242623/500000000000000000)
  k0 := (375267465219783/100000000000000000)
  k6 := (5869558116228881/500000000000000000)
  q := (16496060135680883241/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13606]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13606]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 13532 then ⟨(1139395758128367947023/1000000000000000000000000), (61482698863614156137523/100000000000000000000000), (7992513128765357/1000000000000000000000000)⟩ else
  if n = 13533 then ⟨(284840131185068404963/250000000000000000000000), (307407407476448157783389/500000000000000000000000), (7990973385710239/1000000000000000000000000)⟩ else
  if n = 13534 then ⟨(1139325300084114840733/1000000000000000000000000), (61480264307859040216759/100000000000000000000000), (7989434057196223/1000000000000000000000000)⟩ else
  if n = 13535 then ⟨(284822521039265169527/250000000000000000000000), (614790473012794526324453/1000000000000000000000000), (1597579028616021/200000000000000000000000)⟩ else
  if n = 13536 then ⟨(1139254876956279235641/1000000000000000000000000), (614778304755079583178079/1000000000000000000000000), (3993178321609329/500000000000000000000000)⟩ else
  if n = 13537 then ⟨(569609839239470252439/500000000000000000000000), (614766138305016597248189/1000000000000000000000000), (998102319683593/125000000000000000000000)⟩ else
  if n = 13538 then ⟨(56959224436110782561/50000000000000000000000), (614753973662176653390043/1000000000000000000000000), (997910110710911/125000000000000000000000)⟩ else
  if n = 13539 then ⟨(569574653841638506647/500000000000000000000000), (153685452706532770921337/250000000000000000000000), (3990871813865639/500000000000000000000000)⟩ else
  if n = 13540 then ⟨(284778533839824525581/250000000000000000000000), (76841206224556414130457/125000000000000000000000), (3990103391728881/500000000000000000000000)⟩ else
  if n = 13541 then ⟨(227815794349490720301/200000000000000000000000), (614717490572708904567887/1000000000000000000000000), (159573407054477/20000000000000000000000)⟩ else
  if n = 13542 then ⟨(284760954211229663683/250000000000000000000000), (307352666577237782010149/500000000000000000000000), (7977134335386687/1000000000000000000000000)⟩ else
  if n = 13543 then ⟨(1139008670648870288177/1000000000000000000000000), (614693177541323158701643/1000000000000000000000000), (3987799365651753/500000000000000000000000)⟩ else
  if n = 13544 then ⟨(1138973533156485988071/1000000000000000000000000), (614681023732823669873207/1000000000000000000000000), (7974063540331577/1000000000000000000000000)⟩ else
  if n = 13545 then ⟨(569469202182472915387/500000000000000000000000), (307334435864274597691897/500000000000000000000000), (1993132190582071/250000000000000000000000)⟩ else
  if n = 13546 then ⟨(569451642135714820713/500000000000000000000000), (61465672152807200546337/100000000000000000000000), (3985497198575509/500000000000000000000000)⟩ else
  if n = 13547 then ⟨(1138868172873117705491/1000000000000000000000000), (38415285820685282092523/62500000000000000000000), (1593892088931441/200000000000000000000000)⟩ else
  if n = 13548 then ⟨(1138833070167193604877/1000000000000000000000000), (307316213268399643098777/500000000000000000000000), (1593585380940883/200000000000000000000000)⟩ else
  if n = 13549 then ⟨(142349747018855083779/125000000000000000000000), (1229240563490297909649/2000000000000000000000), (318655751086009/40000000000000000000000)⟩ else
  if n = 13550 then ⟨(1138762890821243399757/1000000000000000000000000), (614608138755586363421179/1000000000000000000000000), (497803816365767/62500000000000000000000)⟩ else
  if n = 13551 then ⟨(1138727814175588166481/1000000000000000000000000), (153648999391921110217743/250000000000000000000000), (7963328758668283/1000000000000000000000000)⟩ else
  if n = 13552 then ⟨(1138692746211060385757/1000000000000000000000000), (122916771636203262241051/200000000000000000000000), (1990449216863991/250000000000000000000000)⟩ else
  if n = 13553 then ⟨(1138657686924850177473/1000000000000000000000000), (76821465074394403109767/125000000000000000000000), (398013269403661/50000000000000000000000)⟩ else
  if n = 13554 then ⟨(1138622636314145288031/1000000000000000000000000), (614559584809674539694039/1000000000000000000000000), (198968358009447/25000000000000000000000)⟩ else
  if n = 13555 then ⟨(142323449297017093841/125000000000000000000000), (614547450824147763626039/1000000000000000000000000), (7957203664227917/1000000000000000000000000)⟩ else
  if n = 13556 then ⟨(569276280554007674359/500000000000000000000000), (4916282549105188228147/8000000000000000000000), (7955673419481309/1000000000000000000000000)⟩ else
  if n = 13557 then ⟨(569258768253487220847/500000000000000000000000), (122904637650250128540161/200000000000000000000000), (994267948249519/125000000000000000000000)⟩ else
  if n = 13558 then ⟨(1138482520570207139181/1000000000000000000000000), (38406941228939252488257/62500000000000000000000), (1988153540907637/250000000000000000000000)⟩ else
  if n = 13559 then ⟨(1138447513294909124783/1000000000000000000000000), (307249466436527381057257/500000000000000000000000), (3975542576121357/500000000000000000000000)⟩ else
  if n = 13560 then ⟨(1138412514678275126749/1000000000000000000000000), (2400339093284785394983/3906250000000000000000), (248423642240339/31250000000000000000000)⟩ else
  if n = 13561 then ⟨(1138377524717502446169/1000000000000000000000000), (122894936937230647301881/200000000000000000000000), (7948028361833263/1000000000000000000000000)⟩ else
  if n = 13562 then ⟨(284585635852447562191/250000000000000000000000), (614462563288373752573073/1000000000000000000000000), (7946500582528359/1000000000000000000000000)⟩ else
  if n = 13563 then ⟨(284576892688084186443/250000000000000000000000), (122890088737428250737331/200000000000000000000000), (3972486606817259/500000000000000000000000)⟩ else
  if n = 13564 then ⟨(227654521348468543517/200000000000000000000000), (61443832588203052051893/100000000000000000000000), (1985861563752559/250000000000000000000000)⟩ else
  if n = 13565 then ⟨(569118825688505051411/500000000000000000000000), (614426209872616386283897/1000000000000000000000000), (794191970651407/100000000000000000000000)⟩ else
  if n = 13566 then ⟨(1138202704653540591033/1000000000000000000000000), (614414095658473937717119/1000000000000000000000000), (1588078713600917/200000000000000000000000)⟩ else
  if n = 13567 then ⟨(1138167766569139140283/1000000000000000000000000), (614401983239178279864061/1000000000000000000000000), (3969433919670243/500000000000000000000000)⟩ else
  if n = 13568 then ⟨(1138132837121009755597/1000000000000000000000000), (122877974522860959561823/200000000000000000000000), (7937342520380461/1000000000000000000000000)⟩ else
  if n = 13569 then ⟨(569048958153179502517/500000000000000000000000), (614377763783428874077051/1000000000000000000000000), (793581761098331/100000000000000000000000)⟩ else
  if n = 13570 then ⟨(569031502061196954829/500000000000000000000000), (153591414186531532582383/250000000000000000000000), (1983573277751967/250000000000000000000000)⟩ else
  if n = 13571 then ⟨(71126756285395165391/62500000000000000000000), (614353551501972247297603/1000000000000000000000000), (7932769020313033/1000000000000000000000000)⟩ else
  if n = 13572 then ⟨(568996602817676922599/500000000000000000000000), (614341448050543117843803/1000000000000000000000000), (7931245338757733/1000000000000000000000000)⟩ else
  if n = 13573 then ⟨(284489579831674849057/250000000000000000000000), (307164673195707373884467/500000000000000000000000), (99121525827513/12500000000000000000000)⟩ else
  if n = 13574 then ⟨(568961720818784768427/500000000000000000000000), (614317246524163217059133/1000000000000000000000000), (7928199202501979/1000000000000000000000000)⟩ else
  if n = 13575 then ⟨(1137888572565177762123/1000000000000000000000000), (76788143556045601484679/125000000000000000000000), (7926676747519717/1000000000000000000000000)⟩ else
  if n = 13576 then ⟨(1137853712106737317873/1000000000000000000000000), (614293052163595973932057/1000000000000000000000000), (3962577350556713/500000000000000000000000)⟩ else
  if n = 13577 then ⟨(1137818860259464003219/1000000000000000000000000), (122856191533886651773189/200000000000000000000000), (1584726612628479/200000000000000000000000)⟩ else
  if n = 13578 then ⟨(1137784017020573368039/1000000000000000000000000), (307134432482726621179629/500000000000000000000000), (3961055916732959/500000000000000000000000)⟩ else
  if n = 13579 then ⟨(1137749182387282114211/1000000000000000000000000), (614256774051232822494577/1000000000000000000000000), (7920591011943349/1000000000000000000000000)⟩ else
  if n = 13580 then ⟨(1137714356356809493239/1000000000000000000000000), (614244684926348993707237/1000000000000000000000000), (98988382480427/12500000000000000000000)⟩ else
  if n = 13581 then ⟨(1137679538926373808533/1000000000000000000000000), (614232597590378740329221/1000000000000000000000000), (3958775296398899/500000000000000000000000)⟩ else
  if n = 13582 then ⟨(1137644730093195911897/1000000000000000000000000), (614220512042899380149791/1000000000000000000000000), (7916030994893829/1000000000000000000000000)⟩ else
  if n = 13583 then ⟨(1137609929854498501703/1000000000000000000000000), (122841685656697650214913/200000000000000000000000), (494656987786369/62500000000000000000000)⟩ else
  if n = 13584 then ⟨(568787569103751315581/500000000000000000000000), (4913570770493782765091/8000000000000000000000), (7912993021721627/1000000000000000000000000)⟩ else
  if n = 13585 then ⟨(227508071029886519413/200000000000000000000000), (614184266127180799287267/1000000000000000000000000), (7911474646172743/1000000000000000000000000)⟩ else
  if n = 13586 then ⟨(1137505580677513842707/1000000000000000000000000), (614172187729439897799491/1000000000000000000000000), (7909956677795059/1000000000000000000000000)⟩ else
  if n = 13587 then ⟨(1137470814788971563227/1000000000000000000000000), (61416011111807807704683/100000000000000000000000), (3954219558224193/500000000000000000000000)⟩ else
  if n = 13588 then ⟨(4443109599535289811/3906250000000000000000), (614148036292673377471883/1000000000000000000000000), (7906921961992679/1000000000000000000000000)⟩ else
  if n = 13589 then ⟨(113740130875092851863/100000000000000000000000), (122827192650560793117627/200000000000000000000000), (1976351303571961/250000000000000000000000)⟩ else
  if n = 13590 then ⟨(1137366568595885267183/1000000000000000000000000), (30706194599902406801313/50000000000000000000000), (1580777774638791/200000000000000000000000)⟩ else
  if n = 13591 then ⟨(113733183701313351913/100000000000000000000000), (614111822527984399046641/1000000000000000000000000), (7902372938571039/1000000000000000000000000)⟩ else
  if n = 13592 then ⟨(142162139249988198667/125000000000000000000000), (122819950968438272830297/200000000000000000000000), (246901794071227/31250000000000000000000)⟩ else
  if n = 13593 then ⟨(1137262399553434239663/1000000000000000000000000), (614087688940247709597191/1000000000000000000000000), (493708893011177/62500000000000000000000)⟩ else
  if n = 13594 then ⟨(1137227693670952679857/1000000000000000000000000), (61407562482173234071967/100000000000000000000000), (7897827572129977/1000000000000000000000000)⟩ else
  if n = 13595 then ⟨(1137192996349695957691/1000000000000000000000000), (614063562486224259999069/1000000000000000000000000), (7896313261993021/1000000000000000000000000)⟩ else
  if n = 13596 then ⟨(284289576896725239219/250000000000000000000000), (1918910943541570569581/3125000000000000000000), (1973699839407093/250000000000000000000000)⟩ else
  if n = 13597 then ⟨(1137123627379803618793/1000000000000000000000000), (307019721581273298746499/500000000000000000000000), (7893285858896419/1000000000000000000000000)⟩ else
  if n = 13598 then ⟨(35534029866426325471/31250000000000000000000), (614027386173535725647759/1000000000000000000000000), (1578354553131533/200000000000000000000000)⟩ else
  if n = 13599 then ⟨(227410858524331252733/200000000000000000000000), (19187979092682797858849/31250000000000000000000), (7890260077772643/1000000000000000000000000)⟩ else
  if n = 13600 then ⟨(1137019638065086609173/1000000000000000000000000), (15350081938476691064939/25000000000000000000000), (1972186948775501/250000000000000000000000)⟩ else
  if n = 13601 then ⟨(284246248013293488753/250000000000000000000000), (306995612946384972164563/500000000000000000000000), (985904489688297/125000000000000000000000)⟩ else
  if n = 13602 then ⟨(1136950354583161330029/1000000000000000000000000), (4911833408212290711337/8000000000000000000000), (7885724444846501/1000000000000000000000000)⟩ else
  if n = 13603 then ⟨(1136915725652292208157/1000000000000000000000000), (306983563969973493146753/500000000000000000000000), (3942106688491577/500000000000000000000000)⟩ else
  if n = 13604 then ⟨(568440552628905946607/500000000000000000000000), (306977540816290998168991/500000000000000000000000), (3941351356888599/500000000000000000000000)⟩ else
  if n = 13605 then ⟨(1136846493396965441817/1000000000000000000000000), (61394303710402186871283/100000000000000000000000), (15762384910179/2000000000000000000000)⟩ else
  ⟨(56840594503350021561/50000000000000000000000), (153482748588461753627431/250000000000000000000000), (3939841300390521/500000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 13532 ≤ n) (hb : n ≤ 13606) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_13532
  · exact row_13533
  · exact row_13534
  · exact row_13535
  · exact row_13536
  · exact row_13537
  · exact row_13538
  · exact row_13539
  · exact row_13540
  · exact row_13541
  · exact row_13542
  · exact row_13543
  · exact row_13544
  · exact row_13545
  · exact row_13546
  · exact row_13547
  · exact row_13548
  · exact row_13549
  · exact row_13550
  · exact row_13551
  · exact row_13552
  · exact row_13553
  · exact row_13554
  · exact row_13555
  · exact row_13556
  · exact row_13557
  · exact row_13558
  · exact row_13559
  · exact row_13560
  · exact row_13561
  · exact row_13562
  · exact row_13563
  · exact row_13564
  · exact row_13565
  · exact row_13566
  · exact row_13567
  · exact row_13568
  · exact row_13569
  · exact row_13570
  · exact row_13571
  · exact row_13572
  · exact row_13573
  · exact row_13574
  · exact row_13575
  · exact row_13576
  · exact row_13577
  · exact row_13578
  · exact row_13579
  · exact row_13580
  · exact row_13581
  · exact row_13582
  · exact row_13583
  · exact row_13584
  · exact row_13585
  · exact row_13586
  · exact row_13587
  · exact row_13588
  · exact row_13589
  · exact row_13590
  · exact row_13591
  · exact row_13592
  · exact row_13593
  · exact row_13594
  · exact row_13595
  · exact row_13596
  · exact row_13597
  · exact row_13598
  · exact row_13599
  · exact row_13600
  · exact row_13601
  · exact row_13602
  · exact row_13603
  · exact row_13604
  · exact row_13605
  · exact row_13606

end BstLean.Part271.R3.Rows13532
