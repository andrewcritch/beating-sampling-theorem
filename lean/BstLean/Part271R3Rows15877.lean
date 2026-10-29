import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15877–15951. -/
namespace BstLean.Part271.R3.Rows15877
open Real BstLean.Part130 BstLean.Part227

theorem width_15877 : mW 15877 = 504300683458113 := by
  have hu : mW 15877 ≤ 504300683458113 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15877 ≤ 504300683458112 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15877 : RowArithmetic 15877 (53792842912915917307/50000000000000000000000) (590476971353089626653333/1000000000000000000000000) (5275104490933763/1000000000000000000000000) where
  r0 := (499858789149/1000000000000000000)
  k0 := (668486168517499/200000000000000000)
  k6 := (2173433763105061/200000000000000000)
  q := (178196520729221871079/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15877]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15877]

theorem width_15878 : mW 15878 = 504411862607794 := by
  have hu : mW 15878 ≤ 504411862607794 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15878 ≤ 504411862607793 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15878 : RowArithmetic 15878 (1075836214008647809251/1000000000000000000000000) (590468100939702054067267/1000000000000000000000000) (5274243099524253/1000000000000000000000000) where
  r0 := (7809555751/15625000000000000)
  k0 := (835568240264911/250000000000000000)
  k6 := (10866826601772783/1000000000000000000)
  q := (178202132422706996069/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15878]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15878]

theorem width_15879 : mW 15879 = 504523059264072 := by
  have hu : mW 15879 ≤ 504523059264072 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15879 ≤ 504523059264071 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15879 : RowArithmetic 15879 (1075815574095838356641/1000000000000000000000000) (295229615808529021809333/500000000000000000000000) (2636690952385351/500000000000000000000000) where
  r0 := (249882177207/500000000000000000)
  k0 := (835528774233453/250000000000000000)
  k6 := (5433242210173891/500000000000000000)
  q := (44551935984870511573/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15879]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15879]

theorem width_15880 : mW 15880 = 504634273428601 := by
  have hu : mW 15880 ≤ 504634273428601 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15880 ≤ 504634273428600 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15880 : RowArithmetic 15880 (2101161989294329819/1953125000000000000000) (295225181692471566443373/500000000000000000000000) (5272520906615457/1000000000000000000000000) where
  r0 := (499717148197/1000000000000000000)
  k0 := (208872328137861/62500000000000000)
  k6 := (10866142271245213/1000000000000000000)
  q := (22276669409945464287/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15880]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15880]

theorem width_15881 : mW 15881 = 504745505103036 := by
  have hu : mW 15881 ≤ 504745505103036 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15881 ≤ 504745505103035 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15881 : RowArithmetic 15881 (1075774307276030359469/1000000000000000000000000) (590441496243143046959753/1000000000000000000000000) (5271660105000877/1000000000000000000000000) where
  r0 := (499669949411/1000000000000000000)
  k0 := (668359884174263/200000000000000000)
  k6 := (2716450038614997/250000000000000000)
  q := (178218966442968689999/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15881]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15881]

theorem width_15882 : mW 15882 = 504856754289030 := by
  have hu : mW 15882 ≤ 504856754289030 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15882 ≤ 504856754289029 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15882 : RowArithmetic 15882 (537876840183323416731/500000000000000000000000) (590432630191443470263311/1000000000000000000000000) (2635399749934681/500000000000000000000000) where
  r0 := (249811379027/500000000000000000)
  k0 := (3341641608926203/1000000000000000000)
  k6 := (10865458069987019/1000000000000000000)
  q := (178224577429713660691/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15882]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15882]

theorem width_15883 : mW 15883 = 504968020988238 := by
  have hu : mW 15883 ≤ 504968020988238 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15883 ≤ 504968020988237 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15883 : RowArithmetic 15883 (537866528894677073717/500000000000000000000000) (590423765229630133219979/1000000000000000000000000) (2634969545581657/500000000000000000000000) where
  r0 := (249787787063/500000000000000000)
  k0 := (1670741907186453/500000000000000000)
  k6 := (543255800891061/50000000000000000)
  q := (178230188239815311037/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15883]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15883]

theorem width_15884 : mW 15884 = 505079305202313 := by
  have hu : mW 15884 ≤ 505079305202313 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15884 ≤ 505079305202312 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15884 : RowArithmetic 15884 (537856219771480570479/500000000000000000000000) (36900931334843057491683/62500000000000000000000) (2634539439412587/500000000000000000000000) where
  r0 := (499528397623/1000000000000000000)
  k0 := (835331509300127/250000000000000000)
  k6 := (5432386998978753/500000000000000000)
  q := (89117899436645161537/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15884]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15884]

theorem width_15885 : mW 15885 = 505190606932910 := by
  have hu : mW 15885 ≤ 505190606932910 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15885 ≤ 505190606932909 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15885 : RowArithmetic 15885 (1075691825626276511369/1000000000000000000000000) (118081207714961137658087/200000000000000000000000) (2634109431398693/500000000000000000000000) where
  r0 := (99896245709/200000000000000000)
  k0 := (1670584138705737/500000000000000000)
  k6 := (2172886402078159/200000000000000000)
  q := (22280176166269422027/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15885]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15885]

theorem width_15886 : mW 15886 = 505301926181683 := by
  have hu : mW 15886 ≤ 505301926181683 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15886 ≤ 505301926181682 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15886 : RowArithmetic 15886 (1075671216038109656137/1000000000000000000000000) (59039717688136638964381/100000000000000000000000) (658419880377803/125000000000000000000000) where
  r0 := (49943406689/100000000000000000)
  k0 := (1670505267500787/500000000000000000)
  k6 := (5432045027558001/500000000000000000)
  q := (178247019610427147249/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15886]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15886]

theorem width_15887 : mW 15887 = 505413262950286 := by
  have hu : mW 15887 ≤ 505413262950286 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15887 ≤ 505413262950285 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15887 : RowArithmetic 15887 (215130122155454078351/200000000000000000000000) (9224817441827453297467/15625000000000000000000) (164578106857587/31250000000000000000000) where
  r0 := (31211682041/62500000000000000)
  k0 := (3340852809966581/1000000000000000000)
  k6 := (5431874066064023/500000000000000000)
  q := (178252629714122310337/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15887]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15887]

theorem width_15888 : mW 15888 = 505524617240373 := by
  have hu : mW 15888 ≤ 505524617240373 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15888 ≤ 505524617240372 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15888 : RowArithmetic 15888 (1075630009842568953551/1000000000000000000000000) (590379456761363636993443/1000000000000000000000000) (5265639992000983/1000000000000000000000000) where
  r0 := (249669882921/500000000000000000)
  k0 := (835173775576403/250000000000000000)
  k6 := (1357925780177731/125000000000000000)
  q := (178258239641257537019/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15888]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15888]

theorem width_15889 : mW 15889 = 505635989053600 := by
  have hu : mW 15889 ≤ 505635989053600 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15889 ≤ 505635989053599 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15889 : RowArithmetic 15889 (1075609413232815435079/1000000000000000000000000) (590370598334372345289129/1000000000000000000000000) (2632390380319769/500000000000000000000000) where
  r0 := (249646313223/500000000000000000)
  k0 := (835134353003609/250000000000000000)
  k6 := (5431532191496163/500000000000000000)
  q := (178263849391849496211/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15889]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15889]

theorem width_15890 : mW 15890 = 505747378391619 := by
  have hu : mW 15890 ≤ 505747378391619 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15890 ≤ 505747378391618 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15890 : RowArithmetic 15890 (1075588820946821469579/1000000000000000000000000) (295180870497884683564509/500000000000000000000000) (1315980431325257/250000000000000000000000) where
  r0 := (249622747233/500000000000000000)
  k0 := (1670189869544411/500000000000000000)
  k6 := (2715680639208601/250000000000000000)
  q := (178269458965914854207/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15890]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15890]

theorem width_15891 : mW 15891 = 505858785256086 := by
  have hu : mW 15891 ≤ 505858785256086 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15891 ≤ 505858785256085 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15891 : RowArithmetic 15891 (67223014561462374233/62500000000000000000000) (147588221186335218450841/250000000000000000000000) (5263062885928013/1000000000000000000000000) where
  r0 := (249599184951/500000000000000000)
  k0 := (3340222083531229/1000000000000000000)
  k6 := (2172476152588601/200000000000000000)
  q := (178275068363470274677/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15891]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15891]

theorem width_15892 : mW 15892 = 505970209648655 := by
  have hu : mW 15892 ≤ 505970209648655 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15892 ≤ 505970209648654 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15892 : RowArithmetic 15892 (107554764934135689889/100000000000000000000000) (590344029582873184267127/1000000000000000000000000) (1052440848492619/200000000000000000000000) where
  r0 := (1996605011/4000000000000000)
  k0 := (1670032222665367/500000000000000000)
  k6 := (10862039001313051/1000000000000000000)
  q := (11142542349033276167/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15892]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15892]

theorem width_15893 : mW 15893 = 506081651570980 := by
  have hu : mW 15893 ≤ 506081651570980 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15893 ≤ 506081651570979 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15893 : RowArithmetic 15893 (537763535009755265153/500000000000000000000000) (18447974234629769307471/31250000000000000000000) (2630672897424447/500000000000000000000000) where
  r0 := (49910414301/100000000000000000)
  k0 := (667981364897959/200000000000000000)
  k6 := (10861697271939469/1000000000000000000)
  q := (8914314331455897231/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15893]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15893]

theorem width_15894 : mW 15894 = 506193111024717 := by
  have hu : mW 15894 ≤ 506193111024717 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15894 ≤ 506193111024716 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15894 : RowArithmetic 15894 (268876623754167766881/250000000000000000000000) (590326322520965625367297/1000000000000000000000000) (1052097508605607/200000000000000000000000) where
  r0 := (499057040679/1000000000000000000)
  k0 := (333974922100083/100000000000000000)
  k6 := (339417361713037/31250000000000000)
  q := (178291895497243508329/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15894]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15894]

theorem width_15895 : mW 15895 = 506304588011520 := by
  have hu : mW 15895 ≤ 506304588011520 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15895 ≤ 506304588011519 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15895 : RowArithmetic 15895 (1075485924331651673589/1000000000000000000000000) (590317470621098640247589/1000000000000000000000000) (262981474347159/50000000000000000000000) where
  r0 := (499009945757/1000000000000000000)
  k0 := (1669795817433149/500000000000000000)
  k6 := (2715253477485281/250000000000000000)
  q := (178297504188925762989/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15895]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15895]

theorem width_15896 : mW 15896 = 506416082533044 := by
  have hu : mW 15896 ≤ 506416082533044 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15896 ≤ 506416082533043 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15896 : RowArithmetic 15896 (1075465357963265649369/1000000000000000000000000) (590308619808338178863317/1000000000000000000000000) (2629385813268503/500000000000000000000000) where
  r0 := (249481429121/500000000000000000)
  k0 := (1669717033040981/500000000000000000)
  k6 := (5430336138653109/500000000000000000)
  q := (178303112704181359169/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15896]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15896]

theorem width_15897 : mW 15897 = 506527594590943 := by
  have hu : mW 15897 ≤ 506527594590943 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15897 ≤ 506527594590942 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15897 : RowArithmetic 15897 (537722397955163496323/500000000000000000000000) (590299770082470843253979/1000000000000000000000000) (2628956980876109/500000000000000000000000) where
  r0 := (498915778131/1000000000000000000)
  k0 := (1669638257320119/500000000000000000)
  k6 := (5430165338453697/500000000000000000)
  q := (178308721043026944819/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15897]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15897]

theorem width_15898 : mW 15898 = 506639124186872 := by
  have hu : mW 15898 ≤ 506639124186872 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15898 ≤ 506639124186871 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15898 : RowArithmetic 15898 (1075424238171649838849/1000000000000000000000000) (147572730360820810468621/250000000000000000000000) (5257056492531533/1000000000000000000000000) where
  r0 := (31179294089/62500000000000000)
  k0 := (3339118980543581/1000000000000000000)
  k6 := (21210916228007/1953125000000000)
  q := (22289291150684895659/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15898]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15898]

theorem width_15899 : mW 15899 = 506750671322486 := by
  have hu : mW 15899 ≤ 506750671322486 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15899 ≤ 506750671322485 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15899 : RowArithmetic 15899 (537701842373024370277/500000000000000000000000) (590282073890562111407041/1000000000000000000000000) (5256199218817691/1000000000000000000000000) where
  r0 := (498821640119/1000000000000000000)
  k0 := (3338961463787753/1000000000000000000)
  k6 := (271491189319943/25000000000000000)
  q := (44579984297888665811/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15899]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15899]

theorem width_15900 : mW 15900 = 506862235999440 := by
  have hu : mW 15900 ≤ 506862235999440 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15900 ≤ 506862235999439 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15900 : RowArithmetic 15900 (1075383135632338667299/1000000000000000000000000) (590273227424094097834167/1000000000000000000000000) (656917767569181/125000000000000000000000) where
  r0 := (498774582213/1000000000000000000)
  k0 := (3338803964365167/1000000000000000000)
  k6 := (2171861213815347/200000000000000000)
  q := (178325545001270078833/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15900]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15900]

theorem width_15901 : mW 15901 = 506973818219390 := by
  have hu : mW 15901 ≤ 506973818219390 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15901 ≤ 506973818219389 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15901 : RowArithmetic 15901 (268840647707333681603/250000000000000000000000) (295132191021833077499669/500000000000000000000000) (656810657210197/125000000000000000000000) where
  r0 := (249363765853/500000000000000000)
  k0 := (133545859291131/40000000000000000)
  k6 := (5429482298785781/500000000000000000)
  q := (178331152634642049521/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15901]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15901]

theorem width_15902 : mW 15902 = 507085417983989 := by
  have hu : mW 15902 ≤ 507085417983989 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15902 ≤ 507085417983988 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15902 : RowArithmetic 15902 (1075342050335853278839/1000000000000000000000000) (295127768874532512627593/500000000000000000000000) (5253628570144897/1000000000000000000000000) where
  r0 := (124670122149/250000000000000000)
  k0 := (1669244508761419/500000000000000000)
  k6 := (678663947392321/62500000000000000)
  q := (89168380045843605087/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15902]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15902]

theorem width_15903 : mW 15903 = 507197035294893 := by
  have hu : mW 15903 ≤ 507197035294893 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15903 ≤ 507197035294892 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15903 : RowArithmetic 15903 (1075321514150710264777/1000000000000000000000000) (295123347270038850707013/500000000000000000000000) (5252772077886221/1000000000000000000000000) where
  r0 := (498633452881/1000000000000000000)
  k0 := (3338331570094611/1000000000000000000)
  k6 := (2171656350237679/200000000000000000)
  q := (44585591843105548261/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15903]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15903]

theorem width_15904 : mW 15904 = 507308670153758 := by
  have hu : mW 15904 ≤ 507308670153758 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15904 ≤ 507308670153757 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15904 : RowArithmetic 15904 (1075300982272722041033/1000000000000000000000000) (59023785241649111776811/100000000000000000000000) (5251915780848381/1000000000000000000000000) where
  r0 := (6232330307/12500000000000000)
  k0 := (33381741399927/10000000000000000)
  k6 := (434317615052011/40000000000000000)
  q := (89173987238431813883/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15904]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15904]

theorem width_15905 : mW 15905 = 507420322562238 := by
  have hu : mW 15905 ≤ 507420322562238 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15905 ≤ 507420322562237 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15905 : RowArithmetic 15905 (43011218188028237519/40000000000000000000000) (590229011378092360684603/1000000000000000000000000) (1312764919743563/250000000000000000000000) where
  r0 := (498539403631/1000000000000000000)
  k0 := (166900836360643/50000000000000000)
  k6 := (2171519806721543/200000000000000000)
  q := (44588395351257035341/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15905]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15905]

theorem width_15906 : mW 15906 = 507531992521989 := by
  have hu : mW 15906 ≤ 507531992521989 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15906 ≤ 507531992521988 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15906 : RowArithmetic 15906 (1075259931433479144449/1000000000000000000000000) (590220171424668493156679/1000000000000000000000000) (5250203772206709/1000000000000000000000000) where
  r0 := (124623097523/250000000000000000)
  k0 := (1668929665875423/500000000000000000)
  k6 := (2171451544621131/200000000000000000)
  q := (178359188156932358247/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15906]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15906]

theorem width_15907 : mW 15907 = 507643680034666 := by
  have hu : mW 15907 ≤ 507643680034666 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15907 ≤ 507643680034665 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15907 : RowArithmetic 15907 (107523941246985954371/100000000000000000000000) (295105666278003334924551/500000000000000000000000) (328084253780541/62500000000000000000000) where
  r0 := (498445383941/1000000000000000000)
  k0 := (3337701953602411/1000000000000000000)
  k6 := (2171383288957807/200000000000000000)
  q := (17836479473259290021/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15907]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15907]

theorem width_15908 : mW 15908 = 507755385101924 := by
  have hu : mW 15908 ≤ 507755385101924 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15908 ≤ 507755385101923 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15908 : RowArithmetic 15908 (1075218897808665434457/1000000000000000000000000) (295101247385947062555433/500000000000000000000000) (2624246271881511/500000000000000000000000) where
  r0 := (249199192589/500000000000000000)
  k0 := (1668772296385003/500000000000000000)
  k6 := (10856575198652797/1000000000000000000)
  q := (178370401132026386437/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15908]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15908]

theorem width_15909 : mW 15909 = 507867107725418 := by
  have hu : mW 15909 ≤ 507867107725418 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15909 ≤ 507867107725417 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15909 : RowArithmetic 15909 (537599193724357765323/500000000000000000000000) (118038731614423615791091/200000000000000000000000) (5247637221972753/1000000000000000000000000) where
  r0 := (2491756969/5000000000000000)
  k0 := (3337387249246033/1000000000000000000)
  k6 := (2171246796938377/200000000000000000)
  q := (178376007355249433501/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15909]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15909]

theorem width_15910 : mW 15910 = 507978847906805 := by
  have hu : mW 15910 ≤ 507978847906805 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15910 ≤ 507978847906804 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15910 : RowArithmetic 15910 (537588940694414202589/500000000000000000000000) (590184822456465878305751/1000000000000000000000000) (2623391047530399/500000000000000000000000) where
  r0 := (249152204903/500000000000000000)
  k0 := (3337229923029593/1000000000000000000)
  k6 := (5427946401450621/500000000000000000)
  q := (178381613402278655363/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15910]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15910]

theorem width_15911 : mW 15911 = 508090605647739 := by
  have hu : mW 15911 ≤ 508090605647739 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15911 ≤ 508090605647738 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15911 : RowArithmetic 15911 (268789344906955970131/250000000000000000000000) (18442999622647653576173/31250000000000000000000) (5245927162970157/1000000000000000000000000) where
  r0 := (249128716597/500000000000000000)
  k0 := (834268153529109/250000000000000000)
  k6 := (10855551653275813/1000000000000000000)
  q := (178387219273130663373/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15911]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15911]

theorem width_15912 : mW 15912 = 508202380949877 := by
  have hu : mW 15912 ≤ 508202380949877 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15912 ≤ 508202380949876 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15912 : RowArithmetic 15912 (1075136882164521359867/1000000000000000000000000) (590167154476682642364387/1000000000000000000000000) (5245072425643819/1000000000000000000000000) where
  r0 := (498210463963/1000000000000000000)
  k0 := (166845766125283/50000000000000000)
  k6 := (2171042107162109/200000000000000000)
  q := (5574775780244439571/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15912]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15912]

theorem width_15913 : mW 15913 = 508314173814873 := by
  have hu : mW 15913 ≤ 508314173814873 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15913 ≤ 508314173814872 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15913 : RowArithmetic 15913 (1075116388997741494973/1000000000000000000000000) (295079161056063262988607/500000000000000000000000) (209768715320993/40000000000000000000000) where
  r0 := (498163502111/1000000000000000000)
  k0 := (1668379024096507/500000000000000000)
  k6 := (2170973890100077/200000000000000000)
  q := (17839843048636947019/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15913]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15913]

theorem width_15914 : mW 15914 = 508425984244383 := by
  have hu : mW 15914 ≤ 508425984244383 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15914 ≤ 508425984244382 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15914 : RowArithmetic 15914 (215019180025260959241/200000000000000000000000) (590149490830844101736979/1000000000000000000000000) (5243363535056219/1000000000000000000000000) where
  r0 := (124529136909/250000000000000000)
  k0 := (1668300395587123/500000000000000000)
  k6 := (5427264198670141/500000000000000000)
  q := (3568080716575789573/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15914]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15914]

theorem width_15915 : mW 15915 = 508537812240064 := by
  have hu : mW 15915 ≤ 508537812240064 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15915 ≤ 508537812240063 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15915 : RowArithmetic 15915 (537537707774515955451/500000000000000000000000) (29507033031631152455479/50000000000000000000000) (1310627345420263/250000000000000000000000) where
  r0 := (498069600537/1000000000000000000)
  k0 := (3336443551448451/1000000000000000000)
  k6 := (2170837475265037/200000000000000000)
  q := (35681928199019738513/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15915]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15915]

theorem width_15916 : mW 15916 = 508649657803571 := by
  have hu : mW 15916 ≤ 508649657803571 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15916 ≤ 508649657803570 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15916 : RowArithmetic 15916 (53752746763237222803/50000000000000000000000) (590131831517250953584909/1000000000000000000000000) (5241655422842419/1000000000000000000000000) where
  r0 := (124505665203/250000000000000000)
  k0 := (208517895563211/62500000000000000)
  k6 := (5426923193725023/500000000000000000)
  q := (89207622992656855121/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15916]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15916]

theorem width_15917 : mW 15917 = 508761520936559 := by
  have hu : mW 15917 ≤ 508761520936559 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15917 ≤ 508761520936558 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15917 : RowArithmetic 15917 (537517229636132231211/500000000000000000000000) (590123003484515623119967/1000000000000000000000000) (2620400829241717/500000000000000000000000) where
  r0 := (497975728459/1000000000000000000)
  k0 := (667225824771753/200000000000000000)
  k6 := (2170701086141963/200000000000000000)
  q := (8921042539972556369/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15917]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15917]

theorem width_15918 : mW 15918 = 508873401640685 := by
  have hu : mW 15918 ≤ 508873401640685 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15918 ≤ 508873401640684 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15918 : RowArithmetic 15918 (67188374223150863737/62500000000000000000000) (23604567061368191166311/40000000000000000000000) (5239948088547211/1000000000000000000000000) where
  r0 := (497928803477/1000000000000000000)
  k0 := (3335971935989713/1000000000000000000)
  k6 := (10853164506099447/1000000000000000000)
  q := (178426455437527537071/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15918]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15918]

theorem width_15919 : mW 15919 = 508985299917604 := by
  have hu : mW 15919 ≤ 508985299917604 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15919 ≤ 508985299917603 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15919 : RowArithmetic 15919 (134374190019751923307/125000000000000000000000) (18440792208315821440767/31250000000000000000000) (5239094712976909/1000000000000000000000000) where
  r0 := (62235235733/125000000000000000)
  k0 := (1667907382699981/500000000000000000)
  k6 := (5426411806806947/500000000000000000)
  q := (178432059899559529801/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15919]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15919]

theorem width_15920 : mW 15920 = 509097215768972 := by
  have hu : mW 15920 ≤ 509097215768972 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15920 ≤ 509097215768971 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15920 : RowArithmetic 15920 (537486528516946078419/500000000000000000000000) (590096525880008020365531/1000000000000000000000000) (5238241531715693/1000000000000000000000000) where
  r0 := (497834975619/1000000000000000000)
  k0 := (667131522417721/200000000000000000)
  k6 := (10852482753248113/1000000000000000000)
  q := (44609416046390923363/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15920]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15920]

theorem width_15921 : mW 15921 = 509209149196446 := by
  have hu : mW 15921 ≤ 509209149196446 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15921 ≤ 509209149196445 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15921 : RowArithmetic 15921 (1074952598196867261817/1000000000000000000000000) (59008770217569798072057/100000000000000000000000) (2618694272353371/500000000000000000000000) where
  r0 := (24889403637/50000000000000000)
  k0 := (3335500476051383/1000000000000000000)
  k6 := (542607096249853/50000000000000000)
  q := (178443268295556613301/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15921]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15921]

theorem width_15922 : mW 15922 = 509321100201681 := by
  have hu : mW 15922 ≤ 509321100201681 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15922 ≤ 509321100201680 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15922 : RowArithmetic 15922 (214986428729152959917/200000000000000000000000) (295039439776482065449563/500000000000000000000000) (5236535751893273/1000000000000000000000000) where
  r0 := (248870588613/500000000000000000)
  k0 := (833835839321847/250000000000000000)
  k6 := (10851801128855691/1000000000000000000)
  q := (89224436114777436009/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15922]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15922]

theorem width_15923 : mW 15923 = 509433068786334 := by
  have hu : mW 15923 ≤ 509433068786334 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15923 ≤ 509433068786333 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15923 : RowArithmetic 15923 (537455846689704363733/500000000000000000000000) (295035029005797288756401/500000000000000000000000) (1308920788304627/250000000000000000000000) where
  r0 := (248847144537/500000000000000000)
  k0 := (208449140986813/62500000000000000)
  k6 := (5425730182409483/500000000000000000)
  q := (178454475987575049673/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15923]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15923]

theorem width_15924 : mW 15924 = 509545054952061 := by
  have hu : mW 15924 ≤ 509545054952061 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15924 ≤ 509545054952060 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15924 : RowArithmetic 15924 (1074891247396623692671/1000000000000000000000000) (295030618775688694595311/500000000000000000000000) (2617415374312847/500000000000000000000000) where
  r0 := (497647408283/1000000000000000000)
  k0 := (3335029171555333/1000000000000000000)
  k6 := (2712779908220461/250000000000000000)
  q := (17846007956963372373/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15924]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15924]

theorem width_15925 : mW 15925 = 509657058700518 := by
  have hu : mW 15925 ≤ 509657058700518 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15925 ≤ 509657058700517 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15925 : RowArithmetic 15925 (214974161139246951013/200000000000000000000000) (118010483634420166090929/200000000000000000000000) (1046795707611621/200000000000000000000000) where
  r0 := (124400133713/250000000000000000)
  k0 := (833718026146363/250000000000000000)
  k6 := (5425389466519643/500000000000000000)
  q := (178465682975747469051/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15925]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15925]

theorem width_15926 : mW 15926 = 509769080033361 := by
  have hu : mW 15926 ≤ 509769080033361 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15926 ≤ 509769080033360 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15926 : RowArithmetic 15926 (537425184138533693489/500000000000000000000000) (73755449984194129200953/125000000000000000000000) (5233126521459031/1000000000000000000000000) where
  r0 := (248776834389/500000000000000000)
  k0 := (3334715054871751/1000000000000000000)
  k6 := (10850438265286253/1000000000000000000)
  q := (178471286205932857899/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15926]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15926]

theorem width_15927 : mW 15927 = 509881118952246 := by
  have hu : mW 15927 ≤ 509881118952246 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15927 ≤ 509881118952245 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15927 : RowArithmetic 15927 (214965987027589494603/200000000000000000000000) (59003478265552241368027/100000000000000000000000) (1046454939754357/200000000000000000000000) where
  r0 := (497506810061/1000000000000000000)
  k0 := (3334558022416667/1000000000000000000)
  k6 := (10850097629617709/1000000000000000000)
  q := (178476889260206459931/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15927]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15927]

theorem width_15928 : mW 15928 = 509993175458831 := by
  have hu : mW 15928 ≤ 509993175458831 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15928 ≤ 509993175458830 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15928 : RowArithmetic 15928 (268702376569425189349/250000000000000000000000) (590025966517797235711923/1000000000000000000000000) (32696394187123/6250000000000000000000) where
  r0 := (248729979349/500000000000000000)
  k0 := (666880201442517/200000000000000000)
  k6 := (5424878513014309/500000000000000000)
  q := (178482492138584842207/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15928]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15928]

theorem width_15929 : mW 15929 = 510105249554770 := by
  have hu : mW 15929 ≤ 510105249554770 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15929 ≤ 510105249554769 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15929 : RowArithmetic 15929 (1074789081695154501603/1000000000000000000000000) (590017151460165934248669/1000000000000000000000000) (523057163490609/100000000000000000000000) where
  r0 := (497413114689/1000000000000000000)
  k0 := (3334244009261943/1000000000000000000)
  k6 := (2169883290902789/200000000000000000)
  q := (5577752963783892787/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15929]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15929]

theorem width_15930 : mW 15930 = 510217341241722 := by
  have hu : mW 15930 ≤ 510217341241722 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15930 ≤ 510217341241721 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15930 : RowArithmetic 15930 (1074768661389134997841/1000000000000000000000000) (147502084370604254383291/250000000000000000000000) (5229720393614361/1000000000000000000000000) where
  r0 := (497366278031/1000000000000000000)
  k0 := (3334087028557121/1000000000000000000)
  k6 := (678067244691791/62500000000000000)
  q := (1115585608548263767/6250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15930]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15930]

theorem width_15931 : mW 15931 = 510329450521342 := by
  have hu : mW 15931 ≤ 510329450521342 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15931 ≤ 510329450521341 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15931 : RowArithmetic 15931 (2686870613396175137/2500000000000000000000) (7374994057304236780813/12500000000000000000000) (653608668250987/125000000000000000000000) where
  r0 := (497319448723/1000000000000000000)
  k0 := (666786013019441/200000000000000000)
  k6 := (10848735407687719/1000000000000000000)
  q := (44624824929628575519/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15931]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15931]

theorem width_15932 : mW 15932 = 510441577395287 := by
  have hu : mW 15932 ≤ 510441577395287 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15932 ≤ 510441577395286 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15932 : RowArithmetic 15932 (26868195840049683511/25000000000000000000000) (589990712765720317669947/1000000000000000000000000) (5228018492030103/1000000000000000000000000) where
  r0 := (497272626763/1000000000000000000)
  k0 := (1666886559438963/500000000000000000)
  k6 := (10848394932366101/1000000000000000000)
  q := (178504901893477423911/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15932]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15932]

theorem width_15933 : mW 15933 = 510553721865214 := by
  have hu : mW 15933 ≤ 510553721865214 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15933 ≤ 510553721865213 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15933 : RowArithmetic 15933 (268676856529628733569/250000000000000000000000) (589981902026349781438587/1000000000000000000000000) (5227167831624409/1000000000000000000000000) where
  r0 := (497225812149/1000000000000000000)
  k0 := (1666808094947507/500000000000000000)
  k6 := (10848054489098773/1000000000000000000)
  q := (178510503892628122289/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15933]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15933]

theorem width_15934 : mW 15934 = 510665883932779 := by
  have hu : mW 15934 ≤ 510665883932779 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15934 ≤ 510665883932778 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15934 : RowArithmetic 15934 (1074687022906881602833/1000000000000000000000000) (36873318272876003218989/62500000000000000000000) (522631736473427/100000000000000000000000) where
  r0 := (497179004881/1000000000000000000)
  k0 := (666691855630181/200000000000000000)
  k6 := (5423857038940353/500000000000000000)
  q := (89258052857991474337/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15934]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15934]

theorem width_15935 : mW 15935 = 510778063599639 := by
  have hu : mW 15935 ≤ 510778063599639 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15935 ≤ 510778063599638 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15935 : RowArithmetic 15935 (214933324793183249577/200000000000000000000000) (589964283784507891471521/1000000000000000000000000) (1306366772825789/250000000000000000000000) where
  r0 := (124283051239/250000000000000000)
  k0 := (133332095345519/40000000000000000)
  k6 := (1084737369870687/100000000000000000)
  q := (178521707363558451937/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15935]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15935]

theorem width_15936 : mW 15936 = 510890260867451 := by
  have hu : mW 15936 ≤ 510890260867451 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15936 ≤ 510890260867450 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15936 : RowArithmetic 15936 (537323114647224091101/500000000000000000000000) (589955476281614045917879/1000000000000000000000000) (2612308505637277/500000000000000000000000) where
  r0 := (124271353093/250000000000000000)
  k0 := (3333145506351951/1000000000000000000)
  k6 := (135587916894653/12500000000000000)
  q := (178527308835371178347/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15936]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15936]

theorem width_15937 : mW 15937 = 511002475737871 := by
  have hu : mW 15937 ≤ 511002475737871 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15937 ≤ 511002475737870 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15937 : RowArithmetic 15937 (537312919445653702351/500000000000000000000000) (589946669857123384543739/1000000000000000000000000) (2611883562295993/500000000000000000000000) where
  r0 := (497038627129/1000000000000000000)
  k0 := (3332988646295267/1000000000000000000)
  k6 := (2711673259117947/250000000000000000)
  q := (5579153441607427237/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15937]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15937]

theorem width_15938 : mW 15938 = 511114708212558 := by
  have hu : mW 15938 ≤ 511114708212558 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15938 ≤ 511114708212557 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15938 : RowArithmetic 15938 (1074605452755323498827/1000000000000000000000000) (294968932255412446047697/500000000000000000000000) (65286467889987/12500000000000000000000) where
  r0 := (62123981153/125000000000000000)
  k0 := (666566360692059/200000000000000000)
  k6 := (10846352753400491/1000000000000000000)
  q := (89269255625887236363/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15938]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15938]

theorem width_15939 : mW 15939 = 511226958293166 := by
  have hu : mW 15939 ≤ 511226958293166 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15939 ≤ 511226958293165 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15939 : RowArithmetic 15939 (537292535442663917463/500000000000000000000000) (589929060242507503301807/1000000000000000000000000) (2611033965519529/500000000000000000000000) where
  r0 := (3882383427/7812500000000000)
  k0 := (666534995569223/200000000000000000)
  k6 := (2711503125588331/250000000000000000)
  q := (178544112196398120263/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15939]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15939]

theorem width_15940 : mW 15940 = 511339225981355 := by
  have hu : mW 15940 ≤ 511339225981355 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15940 ≤ 511339225981354 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15940 : RowArithmetic 15940 (537282346640075271101/500000000000000000000000) (589920257051960245655157/1000000000000000000000000) (5221218624055821/1000000000000000000000000) where
  r0 := (15528072357/31250000000000000)
  k0 := (833129542362951/250000000000000000)
  k6 := (677854517707829/62500000000000000)
  q := (89274856482662575043/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15940]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15940]

theorem width_15941 : mW 15941 = 511451511278780 := by
  have hu : mW 15941 ≤ 511451511278780 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15941 ≤ 511451511278779 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15941 : RowArithmetic 15941 (1074544319938623535791/1000000000000000000000000) (58991145493897227190169/100000000000000000000000) (2610184755096431/500000000000000000000000) where
  r0 := (19874062381/40000000000000000)
  k0 := (3332361378269733/1000000000000000000)
  k6 := (10845332096311291/1000000000000000000)
  q := (35711062711714419099/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15941]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15941]

theorem width_15942 : mW 15942 = 511563814187098 := by
  have hu : mW 15942 ≤ 511563814187098 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15942 ≤ 511563814187097 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15942 : RowArithmetic 15942 (268630987714894647561/250000000000000000000000) (4719221231226661207829/8000000000000000000000) (2609760294696897/500000000000000000000000) where
  r0 := (248402405479/500000000000000000)
  k0 := (3332204604298977/1000000000000000000)
  k6 := (10844991941306383/1000000000000000000)
  q := (44640228494038871799/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15942]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15942]

theorem width_15943 : mW 15943 = 511676134707968 := by
  have hu : mW 15943 ≤ 511676134707968 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15943 ≤ 511676134707967 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15943 : RowArithmetic 15943 (1074503586041847340343/1000000000000000000000000) (589893853944830647581023/1000000000000000000000000) (5218671861602229/1000000000000000000000000) where
  r0 := (248379034861/500000000000000000)
  k0 := (3332047847538613/1000000000000000000)
  k6 := (10844651818305521/1000000000000000000)
  q := (22320814277261481663/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15943]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15943]

theorem width_15944 : mW 15944 = 511788472843045 := by
  have hu : mW 15944 ≤ 511788472843045 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15944 ≤ 511788472843044 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15944 : RowArithmetic 15944 (107448322548426292971/100000000000000000000000) (589885055063255458804081/1000000000000000000000000) (2608911663380921/500000000000000000000000) where
  r0 := (248355667907/500000000000000000)
  k0 := (3331891107981007/1000000000000000000)
  k6 := (1355538965912961/125000000000000000)
  q := (89286057142198859671/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15944]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15944]

theorem width_15945 : mW 15945 = 511900828593988 := by
  have hu : mW 15945 ≤ 511900828593988 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15945 ≤ 511900828593987 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15945 : RowArithmetic 15945 (26861571729641445309/25000000000000000000000) (589876257258396501080277/1000000000000000000000000) (5216974984816287/1000000000000000000000000) where
  r0 := (248332304617/500000000000000000)
  k0 := (832933596407147/250000000000000000)
  k6 := (2168794333659173/200000000000000000)
  q := (178577714175089608241/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15945]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15945]

theorem width_15946 : mW 15946 = 512013201962454 := by
  have hu : mW 15946 ≤ 512013201962454 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15946 ≤ 512013201962453 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15946 : RowArithmetic 15946 (1074442517144865401113/1000000000000000000000000) (589867460530043059923579/1000000000000000000000000) (260806341785463/50000000000000000000000) where
  r0 := (24830894499/50000000000000000)
  k0 := (1665788840238537/500000000000000000)
  k6 := (2710907910319259/250000000000000000)
  q := (178583313890184040341/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15946]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15946]

theorem width_15947 : mW 15947 = 512125592950099 := by
  have hu : mW 15947 ≤ 512125592950099 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15947 ≤ 512125592950098 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15947 : RowArithmetic 15947 (42976886774428791683/40000000000000000000000) (294929332438992308287957/500000000000000000000000) (5215278879384487/1000000000000000000000000) where
  r0 := (496571178049/1000000000000000000)
  k0 := (3331420992518831/1000000000000000000)
  k6 := (2710822911560547/250000000000000000)
  q := (35717782685939506679/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15947]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15947]

theorem width_15948 : mW 15948 = 512238001558582 := by
  have hu : mW 15948 ≤ 512238001558582 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15948 ≤ 512238001558581 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15948 : RowArithmetic 15948 (53720091291602733351/50000000000000000000000) (14746246757550265684673/25000000000000000000000) (1303607778946421/250000000000000000000000) where
  r0 := (496524473441/1000000000000000000)
  k0 := (832816080439071/250000000000000000)
  k6 := (2168590336637261/200000000000000000)
  q := (178594512793646602563/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15948]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15948]

theorem width_15949 : mW 15949 = 512350427789560 := by
  have hu : mW 15949 ≤ 512350427789560 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15949 ≤ 512350427789559 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15949 : RowArithmetic 15949 (107438148655770466537/100000000000000000000000) (294920538400955342042081/500000000000000000000000) (162924485776769/31250000000000000000000) where
  r0 := (248238888077/500000000000000000)
  k0 := (3331107668185149/1000000000000000000)
  k6 := (17348178803367/1600000000000000)
  q := (89300055991023880209/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15949]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15949]

theorem width_15950 : mW 15950 = 512462871644690 := by
  have hu : mW 15950 ≤ 512462871644690 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15950 ≤ 512462871644689 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15950 : RowArithmetic 15950 (214872230307300966989/200000000000000000000000) (589832284377474353327633/1000000000000000000000000) (1303184041635259/250000000000000000000000) where
  r0 := (99286217237/200000000000000000)
  k0 := (3330951031797789/1000000000000000000)
  k6 := (10842271852991387/1000000000000000000)
  q := (11162856937182344809/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15950]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15950]

theorem width_15951 : mW 15951 = 512575333125631 := by
  have hu : mW 15951 ≤ 512575333125631 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15951 ≤ 512575333125630 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15951 : RowArithmetic 15951 (1074340820767290083911/1000000000000000000000000) (294911746514245667166051/500000000000000000000000) (2605944490391373/500000000000000000000000) where
  r0 := (99276880707/200000000000000000)
  k0 := (3330794412599981/1000000000000000000)
  k6 := (1084193198584233/100000000000000000)
  q := (89305654916136189769/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15951]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15951]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 15877 then ⟨(53792842912915917307/50000000000000000000000), (590476971353089626653333/1000000000000000000000000), (5275104490933763/1000000000000000000000000)⟩ else
  if n = 15878 then ⟨(1075836214008647809251/1000000000000000000000000), (590468100939702054067267/1000000000000000000000000), (5274243099524253/1000000000000000000000000)⟩ else
  if n = 15879 then ⟨(1075815574095838356641/1000000000000000000000000), (295229615808529021809333/500000000000000000000000), (2636690952385351/500000000000000000000000)⟩ else
  if n = 15880 then ⟨(2101161989294329819/1953125000000000000000), (295225181692471566443373/500000000000000000000000), (5272520906615457/1000000000000000000000000)⟩ else
  if n = 15881 then ⟨(1075774307276030359469/1000000000000000000000000), (590441496243143046959753/1000000000000000000000000), (5271660105000877/1000000000000000000000000)⟩ else
  if n = 15882 then ⟨(537876840183323416731/500000000000000000000000), (590432630191443470263311/1000000000000000000000000), (2635399749934681/500000000000000000000000)⟩ else
  if n = 15883 then ⟨(537866528894677073717/500000000000000000000000), (590423765229630133219979/1000000000000000000000000), (2634969545581657/500000000000000000000000)⟩ else
  if n = 15884 then ⟨(537856219771480570479/500000000000000000000000), (36900931334843057491683/62500000000000000000000), (2634539439412587/500000000000000000000000)⟩ else
  if n = 15885 then ⟨(1075691825626276511369/1000000000000000000000000), (118081207714961137658087/200000000000000000000000), (2634109431398693/500000000000000000000000)⟩ else
  if n = 15886 then ⟨(1075671216038109656137/1000000000000000000000000), (59039717688136638964381/100000000000000000000000), (658419880377803/125000000000000000000000)⟩ else
  if n = 15887 then ⟨(215130122155454078351/200000000000000000000000), (9224817441827453297467/15625000000000000000000), (164578106857587/31250000000000000000000)⟩ else
  if n = 15888 then ⟨(1075630009842568953551/1000000000000000000000000), (590379456761363636993443/1000000000000000000000000), (5265639992000983/1000000000000000000000000)⟩ else
  if n = 15889 then ⟨(1075609413232815435079/1000000000000000000000000), (590370598334372345289129/1000000000000000000000000), (2632390380319769/500000000000000000000000)⟩ else
  if n = 15890 then ⟨(1075588820946821469579/1000000000000000000000000), (295180870497884683564509/500000000000000000000000), (1315980431325257/250000000000000000000000)⟩ else
  if n = 15891 then ⟨(67223014561462374233/62500000000000000000000), (147588221186335218450841/250000000000000000000000), (5263062885928013/1000000000000000000000000)⟩ else
  if n = 15892 then ⟨(107554764934135689889/100000000000000000000000), (590344029582873184267127/1000000000000000000000000), (1052440848492619/200000000000000000000000)⟩ else
  if n = 15893 then ⟨(537763535009755265153/500000000000000000000000), (18447974234629769307471/31250000000000000000000), (2630672897424447/500000000000000000000000)⟩ else
  if n = 15894 then ⟨(268876623754167766881/250000000000000000000000), (590326322520965625367297/1000000000000000000000000), (1052097508605607/200000000000000000000000)⟩ else
  if n = 15895 then ⟨(1075485924331651673589/1000000000000000000000000), (590317470621098640247589/1000000000000000000000000), (262981474347159/50000000000000000000000)⟩ else
  if n = 15896 then ⟨(1075465357963265649369/1000000000000000000000000), (590308619808338178863317/1000000000000000000000000), (2629385813268503/500000000000000000000000)⟩ else
  if n = 15897 then ⟨(537722397955163496323/500000000000000000000000), (590299770082470843253979/1000000000000000000000000), (2628956980876109/500000000000000000000000)⟩ else
  if n = 15898 then ⟨(1075424238171649838849/1000000000000000000000000), (147572730360820810468621/250000000000000000000000), (5257056492531533/1000000000000000000000000)⟩ else
  if n = 15899 then ⟨(537701842373024370277/500000000000000000000000), (590282073890562111407041/1000000000000000000000000), (5256199218817691/1000000000000000000000000)⟩ else
  if n = 15900 then ⟨(1075383135632338667299/1000000000000000000000000), (590273227424094097834167/1000000000000000000000000), (656917767569181/125000000000000000000000)⟩ else
  if n = 15901 then ⟨(268840647707333681603/250000000000000000000000), (295132191021833077499669/500000000000000000000000), (656810657210197/125000000000000000000000)⟩ else
  if n = 15902 then ⟨(1075342050335853278839/1000000000000000000000000), (295127768874532512627593/500000000000000000000000), (5253628570144897/1000000000000000000000000)⟩ else
  if n = 15903 then ⟨(1075321514150710264777/1000000000000000000000000), (295123347270038850707013/500000000000000000000000), (5252772077886221/1000000000000000000000000)⟩ else
  if n = 15904 then ⟨(1075300982272722041033/1000000000000000000000000), (59023785241649111776811/100000000000000000000000), (5251915780848381/1000000000000000000000000)⟩ else
  if n = 15905 then ⟨(43011218188028237519/40000000000000000000000), (590229011378092360684603/1000000000000000000000000), (1312764919743563/250000000000000000000000)⟩ else
  if n = 15906 then ⟨(1075259931433479144449/1000000000000000000000000), (590220171424668493156679/1000000000000000000000000), (5250203772206709/1000000000000000000000000)⟩ else
  if n = 15907 then ⟨(107523941246985954371/100000000000000000000000), (295105666278003334924551/500000000000000000000000), (328084253780541/62500000000000000000000)⟩ else
  if n = 15908 then ⟨(1075218897808665434457/1000000000000000000000000), (295101247385947062555433/500000000000000000000000), (2624246271881511/500000000000000000000000)⟩ else
  if n = 15909 then ⟨(537599193724357765323/500000000000000000000000), (118038731614423615791091/200000000000000000000000), (5247637221972753/1000000000000000000000000)⟩ else
  if n = 15910 then ⟨(537588940694414202589/500000000000000000000000), (590184822456465878305751/1000000000000000000000000), (2623391047530399/500000000000000000000000)⟩ else
  if n = 15911 then ⟨(268789344906955970131/250000000000000000000000), (18442999622647653576173/31250000000000000000000), (5245927162970157/1000000000000000000000000)⟩ else
  if n = 15912 then ⟨(1075136882164521359867/1000000000000000000000000), (590167154476682642364387/1000000000000000000000000), (5245072425643819/1000000000000000000000000)⟩ else
  if n = 15913 then ⟨(1075116388997741494973/1000000000000000000000000), (295079161056063262988607/500000000000000000000000), (209768715320993/40000000000000000000000)⟩ else
  if n = 15914 then ⟨(215019180025260959241/200000000000000000000000), (590149490830844101736979/1000000000000000000000000), (5243363535056219/1000000000000000000000000)⟩ else
  if n = 15915 then ⟨(537537707774515955451/500000000000000000000000), (29507033031631152455479/50000000000000000000000), (1310627345420263/250000000000000000000000)⟩ else
  if n = 15916 then ⟨(53752746763237222803/50000000000000000000000), (590131831517250953584909/1000000000000000000000000), (5241655422842419/1000000000000000000000000)⟩ else
  if n = 15917 then ⟨(537517229636132231211/500000000000000000000000), (590123003484515623119967/1000000000000000000000000), (2620400829241717/500000000000000000000000)⟩ else
  if n = 15918 then ⟨(67188374223150863737/62500000000000000000000), (23604567061368191166311/40000000000000000000000), (5239948088547211/1000000000000000000000000)⟩ else
  if n = 15919 then ⟨(134374190019751923307/125000000000000000000000), (18440792208315821440767/31250000000000000000000), (5239094712976909/1000000000000000000000000)⟩ else
  if n = 15920 then ⟨(537486528516946078419/500000000000000000000000), (590096525880008020365531/1000000000000000000000000), (5238241531715693/1000000000000000000000000)⟩ else
  if n = 15921 then ⟨(1074952598196867261817/1000000000000000000000000), (59008770217569798072057/100000000000000000000000), (2618694272353371/500000000000000000000000)⟩ else
  if n = 15922 then ⟨(214986428729152959917/200000000000000000000000), (295039439776482065449563/500000000000000000000000), (5236535751893273/1000000000000000000000000)⟩ else
  if n = 15923 then ⟨(537455846689704363733/500000000000000000000000), (295035029005797288756401/500000000000000000000000), (1308920788304627/250000000000000000000000)⟩ else
  if n = 15924 then ⟨(1074891247396623692671/1000000000000000000000000), (295030618775688694595311/500000000000000000000000), (2617415374312847/500000000000000000000000)⟩ else
  if n = 15925 then ⟨(214974161139246951013/200000000000000000000000), (118010483634420166090929/200000000000000000000000), (1046795707611621/200000000000000000000000)⟩ else
  if n = 15926 then ⟨(537425184138533693489/500000000000000000000000), (73755449984194129200953/125000000000000000000000), (5233126521459031/1000000000000000000000000)⟩ else
  if n = 15927 then ⟨(214965987027589494603/200000000000000000000000), (59003478265552241368027/100000000000000000000000), (1046454939754357/200000000000000000000000)⟩ else
  if n = 15928 then ⟨(268702376569425189349/250000000000000000000000), (590025966517797235711923/1000000000000000000000000), (32696394187123/6250000000000000000000)⟩ else
  if n = 15929 then ⟨(1074789081695154501603/1000000000000000000000000), (590017151460165934248669/1000000000000000000000000), (523057163490609/100000000000000000000000)⟩ else
  if n = 15930 then ⟨(1074768661389134997841/1000000000000000000000000), (147502084370604254383291/250000000000000000000000), (5229720393614361/1000000000000000000000000)⟩ else
  if n = 15931 then ⟨(2686870613396175137/2500000000000000000000), (7374994057304236780813/12500000000000000000000), (653608668250987/125000000000000000000000)⟩ else
  if n = 15932 then ⟨(26868195840049683511/25000000000000000000000), (589990712765720317669947/1000000000000000000000000), (5228018492030103/1000000000000000000000000)⟩ else
  if n = 15933 then ⟨(268676856529628733569/250000000000000000000000), (589981902026349781438587/1000000000000000000000000), (5227167831624409/1000000000000000000000000)⟩ else
  if n = 15934 then ⟨(1074687022906881602833/1000000000000000000000000), (36873318272876003218989/62500000000000000000000), (522631736473427/100000000000000000000000)⟩ else
  if n = 15935 then ⟨(214933324793183249577/200000000000000000000000), (589964283784507891471521/1000000000000000000000000), (1306366772825789/250000000000000000000000)⟩ else
  if n = 15936 then ⟨(537323114647224091101/500000000000000000000000), (589955476281614045917879/1000000000000000000000000), (2612308505637277/500000000000000000000000)⟩ else
  if n = 15937 then ⟨(537312919445653702351/500000000000000000000000), (589946669857123384543739/1000000000000000000000000), (2611883562295993/500000000000000000000000)⟩ else
  if n = 15938 then ⟨(1074605452755323498827/1000000000000000000000000), (294968932255412446047697/500000000000000000000000), (65286467889987/12500000000000000000000)⟩ else
  if n = 15939 then ⟨(537292535442663917463/500000000000000000000000), (589929060242507503301807/1000000000000000000000000), (2611033965519529/500000000000000000000000)⟩ else
  if n = 15940 then ⟨(537282346640075271101/500000000000000000000000), (589920257051960245655157/1000000000000000000000000), (5221218624055821/1000000000000000000000000)⟩ else
  if n = 15941 then ⟨(1074544319938623535791/1000000000000000000000000), (58991145493897227190169/100000000000000000000000), (2610184755096431/500000000000000000000000)⟩ else
  if n = 15942 then ⟨(268630987714894647561/250000000000000000000000), (4719221231226661207829/8000000000000000000000), (2609760294696897/500000000000000000000000)⟩ else
  if n = 15943 then ⟨(1074503586041847340343/1000000000000000000000000), (589893853944830647581023/1000000000000000000000000), (5218671861602229/1000000000000000000000000)⟩ else
  if n = 15944 then ⟨(107448322548426292971/100000000000000000000000), (589885055063255458804081/1000000000000000000000000), (2608911663380921/500000000000000000000000)⟩ else
  if n = 15945 then ⟨(26861571729641445309/25000000000000000000000), (589876257258396501080277/1000000000000000000000000), (5216974984816287/1000000000000000000000000)⟩ else
  if n = 15946 then ⟨(1074442517144865401113/1000000000000000000000000), (589867460530043059923579/1000000000000000000000000), (260806341785463/50000000000000000000000)⟩ else
  if n = 15947 then ⟨(42976886774428791683/40000000000000000000000), (294929332438992308287957/500000000000000000000000), (5215278879384487/1000000000000000000000000)⟩ else
  if n = 15948 then ⟨(53720091291602733351/50000000000000000000000), (14746246757550265684673/25000000000000000000000), (1303607778946421/250000000000000000000000)⟩ else
  if n = 15949 then ⟨(107438148655770466537/100000000000000000000000), (294920538400955342042081/500000000000000000000000), (162924485776769/31250000000000000000000)⟩ else
  if n = 15950 then ⟨(214872230307300966989/200000000000000000000000), (589832284377474353327633/1000000000000000000000000), (1303184041635259/250000000000000000000000)⟩ else
  ⟨(1074340820767290083911/1000000000000000000000000), (294911746514245667166051/500000000000000000000000), (2605944490391373/500000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15877 ≤ n) (hb : n ≤ 15951) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15877
  · exact row_15878
  · exact row_15879
  · exact row_15880
  · exact row_15881
  · exact row_15882
  · exact row_15883
  · exact row_15884
  · exact row_15885
  · exact row_15886
  · exact row_15887
  · exact row_15888
  · exact row_15889
  · exact row_15890
  · exact row_15891
  · exact row_15892
  · exact row_15893
  · exact row_15894
  · exact row_15895
  · exact row_15896
  · exact row_15897
  · exact row_15898
  · exact row_15899
  · exact row_15900
  · exact row_15901
  · exact row_15902
  · exact row_15903
  · exact row_15904
  · exact row_15905
  · exact row_15906
  · exact row_15907
  · exact row_15908
  · exact row_15909
  · exact row_15910
  · exact row_15911
  · exact row_15912
  · exact row_15913
  · exact row_15914
  · exact row_15915
  · exact row_15916
  · exact row_15917
  · exact row_15918
  · exact row_15919
  · exact row_15920
  · exact row_15921
  · exact row_15922
  · exact row_15923
  · exact row_15924
  · exact row_15925
  · exact row_15926
  · exact row_15927
  · exact row_15928
  · exact row_15929
  · exact row_15930
  · exact row_15931
  · exact row_15932
  · exact row_15933
  · exact row_15934
  · exact row_15935
  · exact row_15936
  · exact row_15937
  · exact row_15938
  · exact row_15939
  · exact row_15940
  · exact row_15941
  · exact row_15942
  · exact row_15943
  · exact row_15944
  · exact row_15945
  · exact row_15946
  · exact row_15947
  · exact row_15948
  · exact row_15949
  · exact row_15950
  · exact row_15951

end BstLean.Part271.R3.Rows15877
