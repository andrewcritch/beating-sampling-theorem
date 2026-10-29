import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15851–15875. -/
namespace BstLean.Part271.R3.Rows15851
open Real BstLean.Part130 BstLean.Part227

theorem width_15851 : mW 15851 = 501416164965309 := by
  have hu : mW 15851 ≤ 501416164965309 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15851 ≤ 501416164965308 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15851 : RowArithmetic 15851 (538197567453067904301/500000000000000000000000) (590707985655917181545127/1000000000000000000000000) (529756988317653/100000000000000000000000) where
  r0 := (501089152197/1000000000000000000)
  k0 := (836635469888281/250000000000000000)
  k6 := (10876077736750507/1000000000000000000)
  q := (178050554618625100199/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15851]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15851]

theorem width_15852 : mW 15852 = 501526889523793 := by
  have hu : mW 15852 ≤ 501526889523793 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15852 ≤ 501526889523792 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15852 : RowArithmetic 15852 (1076374377477975817503/1000000000000000000000000) (36918692925484461175891/62500000000000000000000) (132417583960223/25000000000000000000000) where
  r0 := (501041737241/1000000000000000000)
  k0 := (167319177228257/50000000000000000)
  k6 := (271893367017309/25000000000000000)
  q := (178056170912439875483/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15852]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15852]

theorem width_15853 : mW 15853 = 501637631545892 := by
  have hu : mW 15853 ≤ 501637631545892 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15853 ≤ 501637631545891 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15853 : RowArithmetic 15853 (269088406104459967733/250000000000000000000000) (590690189055924007024411/1000000000000000000000000) (2647918515901731/500000000000000000000000) where
  r0 := (500994329763/1000000000000000000)
  k0 := (3346225227058551/1000000000000000000)
  k6 := (5437695828547227/500000000000000000)
  q := (178061787029109645517/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15853]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15853]

theorem width_15854 : mW 15854 = 501748391033258 := by
  have hu : mW 15854 ≤ 501748391033258 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15854 ≤ 501748391033257 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15854 : RowArithmetic 15854 (1076332875724524430529/1000000000000000000000000) (590681292400219151558583/1000000000000000000000000) (5294970903301971/1000000000000000000000000) where
  r0 := (3130918311/6250000000000000)
  k0 := (1673033463512909/500000000000000000)
  k6 := (10875048665951671/1000000000000000000)
  q := (1424539223749209371/8000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15854]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15854]

theorem width_15855 : mW 15855 = 501859167987544 := by
  have hu : mW 15855 ≤ 501859167987544 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15855 ≤ 501859167987543 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15855 : RowArithmetic 15855 (538156065698413049279/500000000000000000000000) (590672396840421002956797/1000000000000000000000000) (82720390200723/15625000000000000000000) where
  r0 := (500899537231/1000000000000000000)
  k0 := (1672954322233041/500000000000000000)
  k6 := (10874705707258893/1000000000000000000)
  q := (5564781835346287859/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15855]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15855]

theorem width_15856 : mW 15856 = 501969962410404 := by
  have hu : mW 15856 ≤ 501969962410404 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15856 ≤ 501969962410403 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15856 : RowArithmetic 15856 (538145695716770809119/500000000000000000000000) (7383293779703921317303/12500000000000000000000) (5293239240378203/1000000000000000000000000) where
  r0 := (20034086087/40000000000000000)
  k0 := (1672875189689241/500000000000000000)
  k6 := (10874362781011003/1000000000000000000)
  q := (11129914644776032603/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15856]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15856]

theorem width_15857 : mW 15857 = 502080774303488 := by
  have hu : mW 15857 ≤ 502080774303488 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15857 ≤ 502080774303487 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15857 : RowArithmetic 15857 (1076270655833469291619/1000000000000000000000000) (23626184360307262386249/40000000000000000000000) (330773356614979/62500000000000000000000) where
  r0 := (125201193647/250000000000000000)
  k0 := (418199016469017/125000000000000000)
  k6 := (5437009943601443/500000000000000000)
  q := (178084249724673854999/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15857]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15857]

theorem width_15858 : mW 15858 = 502191603668451 := by
  have hu : mW 15858 ≤ 502191603668451 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15858 ≤ 502191603668450 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15858 : RowArithmetic 15858 (1076249924595406426651/1000000000000000000000000) (73830714591788603632917/125000000000000000000000) (5291508369172523/1000000000000000000000000) where
  r0 := (500757404471/1000000000000000000)
  k0 := (104544809424777/31250000000000000)
  k6 := (2718419256457357/250000000000000000)
  q := (3561797299117399241/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15858]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15858]

theorem width_15859 : mW 15859 = 502302450506945 := by
  have hu : mW 15859 ≤ 502302450506945 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15859 ≤ 502302450506944 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15859 : RowArithmetic 15859 (269057299429537901503/250000000000000000000000) (590636825555979940836023/1000000000000000000000000) (5290643230318703/1000000000000000000000000) where
  r0 := (500710041821/1000000000000000000)
  k0 := (1672637844446561/500000000000000000)
  k6 := (2718333549221379/250000000000000000)
  q := (89047740005010795333/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15859]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15859]

theorem width_15860 : mW 15860 = 502413314820623 := by
  have hu : mW 15860 ≤ 502413314820623 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15860 ≤ 502413314820622 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15860 : RowArithmetic 15860 (1076208475200503552557/1000000000000000000000000) (147656983868119821908951/250000000000000000000000) (661222286152517/125000000000000000000000) where
  r0 := (500662686637/1000000000000000000)
  k0 := (3345117493652047/1000000000000000000)
  k6 := (5436495700183019/500000000000000000)
  q := (22262636860893185759/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15860]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15860]

theorem width_15861 : mW 15861 = 502524196611137 := by
  have hu : mW 15861 ≤ 502524196611137 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15861 ≤ 502524196611136 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15861 : RowArithmetic 15861 (538093878520630847919/500000000000000000000000) (73827380810448929004321/125000000000000000000000) (2644456772909393/500000000000000000000000) where
  r0 := (500615338917/1000000000000000000)
  k0 := (1672479657932717/500000000000000000)
  k6 := (10872648636265883/1000000000000000000)
  q := (89053354793629195427/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15861]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15861]

theorem width_15862 : mW 15862 = 502635095880141 := by
  have hu : mW 15862 ≤ 502635095880141 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15862 ≤ 502635095880140 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15862 : RowArithmetic 15862 (538083521619612661209/500000000000000000000000) (295305079294550404564103/500000000000000000000000) (5288049000056619/1000000000000000000000000) where
  r0 := (500567998659/1000000000000000000)
  k0 := (1672400577764539/500000000000000000)
  k6 := (10872305904579941/1000000000000000000)
  q := (1113202025689856531/6250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15862]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15862]

theorem width_15863 : mW 15863 = 502746012629287 := by
  have hu : mW 15863 ≤ 502746012629287 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15863 ≤ 502746012629286 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15863 : RowArithmetic 15863 (538073166896597354131/500000000000000000000000) (295300635894396068666813/500000000000000000000000) (2643592325937821/500000000000000000000000) where
  r0 := (500520665861/1000000000000000000)
  k0 := (3344643012638771/1000000000000000000)
  k6 := (169874425082861/15625000000000000)
  q := (178117938456518185697/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15863]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15863]

theorem width_15864 : mW 15864 = 502856946860230 := by
  have hu : mW 15864 ≤ 502856946860230 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15864 ≤ 502856946860229 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15864 : RowArithmetic 15864 (538062814350984851797/500000000000000000000000) (118118477216490004749391/200000000000000000000000) (1321580125304463/250000000000000000000000) where
  r0 := (500473340523/1000000000000000000)
  k0 := (3344484887196989/1000000000000000000)
  k6 := (2174324107686053/200000000000000000)
  q := (89061776312849273869/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15864]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15864]

theorem width_15865 : mW 15865 = 502967898574620 := by
  have hu : mW 15865 ≤ 502967898574620 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15865 ≤ 502967898574619 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15865 : RowArithmetic 15865 (107610492796435199569/100000000000000000000000) (147645875367464803993701/250000000000000000000000) (5285456548025319/1000000000000000000000000) where
  r0 := (250213011321/500000000000000000)
  k0 := (3344326779196181/1000000000000000000)
  k6 := (10871277903956317/1000000000000000000)
  q := (44532291654483715779/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15865]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15865]

theorem width_15866 : mW 15866 = 503078867774113 := by
  have hu : mW 15866 ≤ 503078867774113 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15866 ≤ 503078867774112 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15866 : RowArithmetic 15866 (134510528947392749721/125000000000000000000000) (295287308975402234814267/500000000000000000000000) (2642296396120037/500000000000000000000000) where
  r0 := (500378712217/1000000000000000000)
  k0 := (3344168688635481/1000000000000000000)
  k6 := (2174187060375231/200000000000000000)
  q := (44533695108310965307/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15866]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15866]

theorem width_15867 : mW 15867 = 503189854460361 := by
  have hu : mW 15867 ≤ 503189854460361 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15867 ≤ 503189854460360 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15867 : RowArithmetic 15867 (1076063539545141676617/1000000000000000000000000) (2306897404394807283227/3906250000000000000000) (330233077112763/62500000000000000000000) where
  r0 := (250165704623/500000000000000000)
  k0 := (1672005307755339/500000000000000000)
  k6 := (2717648183046169/250000000000000000)
  q := (44535098517910567209/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15867]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15867]

theorem width_15868 : mW 15868 = 503300858635017 := by
  have hu : mW 15868 ≤ 503300858635017 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15868 ≤ 503300858635016 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15868 : RowArithmetic 15868 (538021425930576569249/500000000000000000000000) (147639213548110661055861/250000000000000000000000) (211314634906393/40000000000000000000000) where
  r0 := (500284113727/1000000000000000000)
  k0 := (3343852559817561/1000000000000000000)
  k6 := (434810007795071/40000000000000000)
  q := (89073003766573405033/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15868]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15868]

theorem width_15869 : mW 15869 = 503411880299735 := by
  have hu : mW 15869 ≤ 503411880299735 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15869 ≤ 503411880299734 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15869 : RowArithmetic 15869 (538011084262989314731/500000000000000000000000) (23621918958108216888989/40000000000000000000000) (5282002708749039/1000000000000000000000000) where
  r0 := (500236825659/1000000000000000000)
  k0 := (3343694521555259/1000000000000000000)
  k6 := (1358738461243419/125000000000000000)
  q := (22268952602221775801/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15869]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15869]

theorem width_15870 : mW 15870 = 503522919456168 := by
  have hu : mW 15870 ≤ 503522919456168 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15870 ≤ 503522919456167 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15870 : RowArithmetic 15870 (1076001489538421100003/1000000000000000000000000) (59053909480564397292857/100000000000000000000000) (1056227948402799/200000000000000000000000) where
  r0 := (500189545041/1000000000000000000)
  k0 := (3343536500722903/1000000000000000000)
  k6 := (2173913043478261/200000000000000000)
  q := (178157233925541176719/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15870]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15870]

theorem width_15871 : mW 15871 = 503633976105970 := by
  have hu : mW 15871 ≤ 503633976105970 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15871 ≤ 503633976105969 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15871 : RowArithmetic 15871 (1075980814897283640231/1000000000000000000000000) (590530216751043438987873/1000000000000000000000000) (5280276972396851/1000000000000000000000000) where
  r0 := (500142271869/1000000000000000000)
  k0 := (3343378497309593/1000000000000000000)
  k6 := (2173844555440707/200000000000000000)
  q := (89081423428232218611/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15871]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15871]

theorem width_15872 : mW 15872 = 503745050250793 := by
  have hu : mW 15872 ≤ 503745050250793 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15872 ≤ 503745050250792 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15872 : RowArithmetic 15872 (1075960144601370326061/1000000000000000000000000) (590521339788688842956243/1000000000000000000000000) (1055882879967961/200000000000000000000000) where
  r0 := (7813984471/15625000000000000)
  k0 := (3343220511321143/1000000000000000000)
  k6 := (84913127885773/7812500000000000)
  q := (44542114902640175377/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15872]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15872]

theorem width_15873 : mW 15873 = 503856141892292 := by
  have hu : mW 15873 ≤ 503856141892292 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15873 ≤ 503856141892291 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15873 : RowArithmetic 15873 (1075939478649484808727/1000000000000000000000000) (118102492783673095773879/200000000000000000000000) (5278552024285047/1000000000000000000000000) where
  r0 := (500047747863/1000000000000000000)
  k0 := (1671531271374997/500000000000000000)
  k6 := (2173707598782487/200000000000000000)
  q := (89087036093923340267/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15873]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15873]

theorem width_15874 : mW 15874 = 503967251032120 := by
  have hu : mW 15874 ≤ 503967251032120 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15874 ≤ 503967251032119 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15874 : RowArithmetic 15874 (537959408520215862443/500000000000000000000000) (590503589139858547026843/1000000000000000000000000) (1055537969134961/200000000000000000000000) where
  r0 := (20000019881/40000000000000000)
  k0 := (417863073949409/125000000000000000)
  k6 := (10868195650798911/1000000000000000000)
  q := (1425437476706712661/8000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15874]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15874]

theorem width_15875 : mW 15875 = 504078377671930 := by
  have hu : mW 15875 ≤ 504078377671930 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15875 ≤ 504078377671929 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15875 : RowArithmetic 15875 (1075898159773016132103/1000000000000000000000000) (590494715452953315988987/1000000000000000000000000) (2638413931975667/500000000000000000000000) where
  r0 := (499953253627/1000000000000000000)
  k0 := (1671373328924709/500000000000000000)
  k6 := (10867853340033277/1000000000000000000)
  q := (44546324203013653369/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15875]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15875]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 15851 then ⟨(538197567453067904301/500000000000000000000000), (590707985655917181545127/1000000000000000000000000), (529756988317653/100000000000000000000000)⟩ else
  if n = 15852 then ⟨(1076374377477975817503/1000000000000000000000000), (36918692925484461175891/62500000000000000000000), (132417583960223/25000000000000000000000)⟩ else
  if n = 15853 then ⟨(269088406104459967733/250000000000000000000000), (590690189055924007024411/1000000000000000000000000), (2647918515901731/500000000000000000000000)⟩ else
  if n = 15854 then ⟨(1076332875724524430529/1000000000000000000000000), (590681292400219151558583/1000000000000000000000000), (5294970903301971/1000000000000000000000000)⟩ else
  if n = 15855 then ⟨(538156065698413049279/500000000000000000000000), (590672396840421002956797/1000000000000000000000000), (82720390200723/15625000000000000000000)⟩ else
  if n = 15856 then ⟨(538145695716770809119/500000000000000000000000), (7383293779703921317303/12500000000000000000000), (5293239240378203/1000000000000000000000000)⟩ else
  if n = 15857 then ⟨(1076270655833469291619/1000000000000000000000000), (23626184360307262386249/40000000000000000000000), (330773356614979/62500000000000000000000)⟩ else
  if n = 15858 then ⟨(1076249924595406426651/1000000000000000000000000), (73830714591788603632917/125000000000000000000000), (5291508369172523/1000000000000000000000000)⟩ else
  if n = 15859 then ⟨(269057299429537901503/250000000000000000000000), (590636825555979940836023/1000000000000000000000000), (5290643230318703/1000000000000000000000000)⟩ else
  if n = 15860 then ⟨(1076208475200503552557/1000000000000000000000000), (147656983868119821908951/250000000000000000000000), (661222286152517/125000000000000000000000)⟩ else
  if n = 15861 then ⟨(538093878520630847919/500000000000000000000000), (73827380810448929004321/125000000000000000000000), (2644456772909393/500000000000000000000000)⟩ else
  if n = 15862 then ⟨(538083521619612661209/500000000000000000000000), (295305079294550404564103/500000000000000000000000), (5288049000056619/1000000000000000000000000)⟩ else
  if n = 15863 then ⟨(538073166896597354131/500000000000000000000000), (295300635894396068666813/500000000000000000000000), (2643592325937821/500000000000000000000000)⟩ else
  if n = 15864 then ⟨(538062814350984851797/500000000000000000000000), (118118477216490004749391/200000000000000000000000), (1321580125304463/250000000000000000000000)⟩ else
  if n = 15865 then ⟨(107610492796435199569/100000000000000000000000), (147645875367464803993701/250000000000000000000000), (5285456548025319/1000000000000000000000000)⟩ else
  if n = 15866 then ⟨(134510528947392749721/125000000000000000000000), (295287308975402234814267/500000000000000000000000), (2642296396120037/500000000000000000000000)⟩ else
  if n = 15867 then ⟨(1076063539545141676617/1000000000000000000000000), (2306897404394807283227/3906250000000000000000), (330233077112763/62500000000000000000000)⟩ else
  if n = 15868 then ⟨(538021425930576569249/500000000000000000000000), (147639213548110661055861/250000000000000000000000), (211314634906393/40000000000000000000000)⟩ else
  if n = 15869 then ⟨(538011084262989314731/500000000000000000000000), (23621918958108216888989/40000000000000000000000), (5282002708749039/1000000000000000000000000)⟩ else
  if n = 15870 then ⟨(1076001489538421100003/1000000000000000000000000), (59053909480564397292857/100000000000000000000000), (1056227948402799/200000000000000000000000)⟩ else
  if n = 15871 then ⟨(1075980814897283640231/1000000000000000000000000), (590530216751043438987873/1000000000000000000000000), (5280276972396851/1000000000000000000000000)⟩ else
  if n = 15872 then ⟨(1075960144601370326061/1000000000000000000000000), (590521339788688842956243/1000000000000000000000000), (1055882879967961/200000000000000000000000)⟩ else
  if n = 15873 then ⟨(1075939478649484808727/1000000000000000000000000), (118102492783673095773879/200000000000000000000000), (5278552024285047/1000000000000000000000000)⟩ else
  if n = 15874 then ⟨(537959408520215862443/500000000000000000000000), (590503589139858547026843/1000000000000000000000000), (1055537969134961/200000000000000000000000)⟩ else
  ⟨(1075898159773016132103/1000000000000000000000000), (590494715452953315988987/1000000000000000000000000), (2638413931975667/500000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15851 ≤ n) (hb : n ≤ 15875) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15851
  · exact row_15852
  · exact row_15853
  · exact row_15854
  · exact row_15855
  · exact row_15856
  · exact row_15857
  · exact row_15858
  · exact row_15859
  · exact row_15860
  · exact row_15861
  · exact row_15862
  · exact row_15863
  · exact row_15864
  · exact row_15865
  · exact row_15866
  · exact row_15867
  · exact row_15868
  · exact row_15869
  · exact row_15870
  · exact row_15871
  · exact row_15872
  · exact row_15873
  · exact row_15874
  · exact row_15875

end BstLean.Part271.R3.Rows15851
