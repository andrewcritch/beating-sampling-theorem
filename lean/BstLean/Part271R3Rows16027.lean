import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 16027–16101. -/
namespace BstLean.Part271.R3.Rows16027
open Real BstLean.Part130 BstLean.Part227

theorem width_16027 : mW 16027 = 521174104976760 := by
  have hu : mW 16027 ≤ 521174104976760 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16027 ≤ 521174104976759 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16027 : RowArithmetic 16027 (107280803559880690789/100000000000000000000000) (589158481364631722635027/1000000000000000000000000) (1029612407926963/200000000000000000000000) where
  r0 := (98571562381/200000000000000000)
  k0 := (829735352992023/250000000000000000)
  k6 := (1081619522943629/100000000000000000)
  q := (89518154583302263247/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16027]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16027]

theorem width_16028 : mW 16028 = 521287928626871 := by
  have hu : mW 16028 ≤ 521287928626871 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16028 ≤ 521287928626870 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16028 : RowArithmetic 16028 (1072788028765789931153/1000000000000000000000000) (589149772198336772675323/1000000000000000000000000) (2573614756783681/500000000000000000000000) where
  r0 := (492811687923/1000000000000000000)
  k0 := (829696526790031/250000000000000000)
  k6 := (5407928904274819/500000000000000000)
  q := (179041894538680527223/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16028]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16028]

theorem width_16029 : mW 16029 = 521401770032242 := by
  have hu : mW 16029 ≤ 521401770032242 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16029 ≤ 521401770032241 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16029 : RowArithmetic 16029 (1072768026095113380927/1000000000000000000000000) (589141064091261103843289/1000000000000000000000000) (2573198587867023/500000000000000000000000) where
  r0 := (246382785567/500000000000000000)
  k0 := (414828852413199/125000000000000000)
  k6 := (2163104083847891/200000000000000000)
  q := (22380934967065160569/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16029]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16029]

theorem width_16030 : mW 16030 = 521515629194536 := by
  have hu : mW 16030 ≤ 521515629194536 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16030 ≤ 521515629194535 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16030 : RowArithmetic 16030 (1072748027585642848057/1000000000000000000000000) (589132357043198802582531/1000000000000000000000000) (25727825130401/5000000000000000000000) where
  r0 := (246359730769/500000000000000000)
  k0 := (1659237774203437/500000000000000000)
  k6 := (10815183061500817/1000000000000000000)
  q := (179053064760143103227/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16030]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16030]

theorem width_16031 : mW 16031 = 521629506115414 := by
  have hu : mW 16031 ≤ 521629506115414 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16031 ≤ 521629506115413 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16031 : RowArithmetic 16031 (1072728033236244851573/1000000000000000000000000) (3682022819087149809153/6250000000000000000000) (5144733064551201/1000000000000000000000000) where
  r0 := (123168339783/250000000000000000)
  k0 := (414790036807031/125000000000000000)
  k6 := (13518557169161/1250000000000000)
  q := (44764662402390571363/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16031]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16031]

theorem width_16032 : mW 16032 = 521743400796538 := by
  have hu : mW 16032 ≤ 521743400796538 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16032 ≤ 521743400796537 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16032 : RowArithmetic 16032 (268177010761446509897/250000000000000000000000) (294557473061645367684809/500000000000000000000000) (5143901291092433/1000000000000000000000000) where
  r0 := (98525452783/200000000000000000)
  k0 := (1659082528726363/500000000000000000)
  k6 := (10814508440718481/1000000000000000000)
  q := (179064234284795130889/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16032]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16032]

theorem width_16033 : mW 16033 = 521857313239569 := by
  have hu : mW 16033 ≤ 521857313239569 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16033 ≤ 521857313239568 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16033 : RowArithmetic 16033 (214537611402626744277/200000000000000000000000) (117821248450206679108581/200000000000000000000000) (5143069705649311/1000000000000000000000000) where
  r0 := (246290587943/500000000000000000)
  k0 := (1659004918697659/500000000000000000)
  k6 := (10814171177664939/1000000000000000000)
  q := (179069818785857936659/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16033]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16033]

theorem width_16034 : mW 16034 = 521971243446170 := by
  have hu : mW 16034 ≤ 521971243446170 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16034 ≤ 521971243446169 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16034 : RowArithmetic 16034 (1072668075137155069377/1000000000000000000000000) (589097539436966228458373/1000000000000000000000000) (5142238308167251/1000000000000000000000000) where
  r0 := (492535095043/1000000000000000000)
  k0 := (1658927317139833/500000000000000000)
  k6 := (5406916973081627/500000000000000000)
  q := (8953770155638349867/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16034]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16034]

theorem width_16035 : mW 16035 = 522085191418003 := by
  have hu : mW 16035 ≤ 522085191418003 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16035 ≤ 522085191418002 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16035 : RowArithmetic 16035 (1072648097416717916981/1000000000000000000000000) (589088837680883548799589/1000000000000000000000000) (5141407098591697/1000000000000000000000000) where
  r0 := (492489021383/1000000000000000000)
  k0 := (1658849724049021/500000000000000000)
  k6 := (5406748373104253/500000000000000000)
  q := (179080987265538604971/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16035]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16035]

theorem width_16036 : mW 16036 = 522199157156729 := by
  have hu : mW 16036 ≤ 522199157156729 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16036 ≤ 522199157156728 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16036 : RowArithmetic 16036 (268157030962672689489/250000000000000000000000) (73635017122822468590187/125000000000000000000000) (5140576076868123/1000000000000000000000000) where
  r0 := (492442954907/1000000000000000000)
  k0 := (6479578669641/1953125000000000)
  k6 := (10813159577795777/1000000000000000000)
  q := (179086571244189049051/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16036]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16036]

theorem width_16037 : mW 16037 = 522313140664011 := by
  have hu : mW 16037 ≤ 522313140664011 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16037 ≤ 522313140664010 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16037 : RowArithmetic 16037 (26815203860948548731/25000000000000000000000) (117814287468369856916517/200000000000000000000000) (5139745242942003/1000000000000000000000000) where
  r0 := (123099223903/250000000000000000)
  k0 := (3317389126546387/1000000000000000000)
  k6 := (216256448818403/20000000000000000)
  q := (89546077524367308269/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16037]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16037]

theorem width_16038 : mW 16038 = 522427141941510 := by
  have hu : mW 16038 ≤ 522427141941510 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16038 ≤ 522427141941509 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16038 : RowArithmetic 16038 (134073523647167596669/125000000000000000000000) (589062738758486660644693/1000000000000000000000000) (5138914596758853/1000000000000000000000000) where
  r0 := (61543855437/125000000000000000)
  k0 := (1658616995582133/500000000000000000)
  k6 := (2703121333894177/250000000000000000)
  q := (179097738679191591853/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16038]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16038]

theorem width_16039 : mW 16039 = 522541160990889 := by
  have hu : mW 16039 ≤ 522541160990889 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16039 ≤ 522541160990888 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16039 : RowArithmetic 16039 (1072568228067756376021/1000000000000000000000000) (368158775770179038533/625000000000000000000) (2569042069132093/500000000000000000000000) where
  r0 := (492304798559/1000000000000000000)
  k0 := (1658539436356101/500000000000000000)
  k6 := (5406074130880269/500000000000000000)
  q := (44775830533894064219/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16039]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16039]

theorem width_16040 : mW 16040 = 522655197813810 := by
  have hu : mW 16040 ≤ 522655197813810 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16040 ≤ 522655197813809 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16040 : RowArithmetic 16040 (536274135554029281303/500000000000000000000000) (73630668095380409309407/125000000000000000000000) (2568626933701773/500000000000000000000000) where
  r0 := (246129380399/500000000000000000)
  k0 := (663384754236493/200000000000000000)
  k6 := (432472448778669/40000000000000000)
  q := (179108905417904890953/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16040]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16040]

theorem width_16041 : mW 16041 = 522769252411936 := by
  have hu : mW 16041 ≤ 522769252411936 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16041 ≤ 522769252411935 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16041 : RowArithmetic 16041 (536264159148558633603/500000000000000000000000) (589036649350551772514413/1000000000000000000000000) (2568211892061243/500000000000000000000000) where
  r0 := (492212730211/1000000000000000000)
  k0 := (3316768686570689/1000000000000000000)
  k6 := (2162294841738071/200000000000000000)
  q := (179114488526193770889/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16041]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16041]

theorem width_16042 : mW 16042 = 522883324786927 := by
  have hu : mW 16042 ≤ 522883324786927 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16042 ≤ 522883324786926 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16042 : RowArithmetic 16042 (13406354620422545163/12500000000000000000000) (294513977497303345804539/500000000000000000000000) (513559388836661/100000000000000000000000) where
  r0 := (492166706799/1000000000000000000)
  k0 := (1658306809441309/500000000000000000)
  k6 := (5405568614713259/500000000000000000)
  q := (35824014292091834191/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16042]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16042]

theorem width_16043 : mW 16043 = 522997414940448 := by
  have hu : mW 16043 ≤ 522997414940448 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16043 ≤ 522997414940447 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16043 : RowArithmetic 16043 (1072488425116987791441/1000000000000000000000000) (589019261695002768526281/1000000000000000000000000) (1283691045020373/250000000000000000000000) where
  r0 := (492120690557/1000000000000000000)
  k0 := (3316458568103777/1000000000000000000)
  k6 := (10810800281670303/1000000000000000000)
  q := (44781413555179340721/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16043]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16043]

theorem width_16044 : mW 16044 = 523111522874160 := by
  have hu : mW 16044 ≤ 523111522874160 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16044 ≤ 523111522874159 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16044 : RowArithmetic 16044 (134058560593192680941/125000000000000000000000) (294505284725767452913789/500000000000000000000000) (1283483664803191/250000000000000000000000) where
  r0 := (492074681487/1000000000000000000)
  k0 := (1658151767121639/500000000000000000)
  k6 := (10810463365416799/1000000000000000000)
  q := (89565618403492307937/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16044]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16044]

theorem width_16045 : mW 16045 = 523225648589726 := by
  have hu : mW 16045 ≤ 523225648589726 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16045 ≤ 523225648589725 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16045 : RowArithmetic 16045 (536224274259168044859/500000000000000000000000) (589001878263997955198781/1000000000000000000000000) (5133105325706059/1000000000000000000000000) where
  r0 := (15375896237/31250000000000000)
  k0 := (3316148517286643/1000000000000000000)
  k6 := (10810126480661099/1000000000000000000)
  q := (44784204804819299147/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16045]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16045]

theorem width_16046 : mW 16046 = 523339792088808 := by
  have hu : mW 16046 ≤ 523339792088808 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16046 ≤ 523339792088807 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16046 : RowArithmetic 16046 (1072428616434243884417/1000000000000000000000000) (36812074258261677316917/62500000000000000000000) (32076726121919/6250000000000000000000) where
  r0 := (491982684849/1000000000000000000)
  k0 := (663198703447923/200000000000000000)
  k6 := (2161957925479659/200000000000000000)
  q := (35828480291522273831/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16046]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16046]

theorem width_16047 : mW 16047 = 523453953373068 := by
  have hu : mW 16047 ≤ 523453953373068 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16047 ≤ 523453953373067 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16047 : RowArithmetic 16047 (1072408688492137390823/1000000000000000000000000) (588984499055896616750713/1000000000000000000000000) (1282861805140347/250000000000000000000000) where
  r0 := (1537302179/3125000000000000)
  k0 := (103619954190557/31250000000000000)
  k6 := (270236320140587/25000000000000000)
  q := (17914798352200339517/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16047]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16047]

theorem width_16048 : mW 16048 = 523568132444170 := by
  have hu : mW 16048 ≤ 523568132444170 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16048 ≤ 523568132444169 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16048 : RowArithmetic 16048 (1072388764690889031857/1000000000000000000000000) (147243952758730564737967/250000000000000000000000) (5130618448814787/1000000000000000000000000) where
  r0 := (245945358437/500000000000000000)
  k0 := (414460445981691/125000000000000000)
  k6 := (10809116015331749/1000000000000000000)
  q := (179153565412469533693/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16048]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16048]

theorem width_16049 : mW 16049 = 523682329303776 := by
  have hu : mW 16049 ≤ 523682329303776 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16049 ≤ 523682329303775 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16049 : RowArithmetic 16049 (214473769005874430469/200000000000000000000000) (588967124069058951418531/1000000000000000000000000) (2564894932106479/500000000000000000000000) where
  r0 := (491844743631/1000000000000000000)
  k0 := (3315528618509099/1000000000000000000)
  k6 := (5404389628259099/500000000000000000)
  q := (89579573564513020627/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16049]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16049]

theorem width_16050 : mW 16050 = 523796543953549 := by
  have hu : mW 16050 ≤ 523796543953549 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16050 ≤ 523796543953548 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16050 : RowArithmetic 16050 (536174464753230112559/500000000000000000000000) (588958438158101811993813/1000000000000000000000000) (5128961466701633/1000000000000000000000000) where
  r0 := (122949694387/250000000000000000)
  k0 := (414421710757099/125000000000000000)
  k6 := (10808442529177923/1000000000000000000)
  q := (179164728671689171847/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16050]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16050]

theorem width_16051 : mW 16051 = 523910776395151 := by
  have hu : mW 16051 ≤ 523910776395151 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16051 ≤ 523910776395150 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16051 : RowArithmetic 16051 (536164509060513689817/500000000000000000000000) (294474876650923014316567/500000000000000000000000) (1282033314056643/250000000000000000000000) where
  r0 := (3934022549/8000000000000000)
  k0 := (1657609385249489/500000000000000000)
  k6 := (10808105833306023/1000000000000000000)
  q := (89585155020237588469/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16051]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16051]

theorem width_16052 : mW 16052 = 524025026630246 := by
  have hu : mW 16052 ≤ 524025026630246 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16052 ≤ 524025026630245 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16052 : RowArithmetic 16052 (1072309110871947609133/1000000000000000000000000) (294470534750043468499781/500000000000000000000000) (5127305232733537/1000000000000000000000000) where
  r0 := (491706866859/1000000000000000000)
  k0 := (331506387182791/100000000000000000)
  k6 := (10807769168897597/1000000000000000000)
  q := (8958794561770015273/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16052]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16052]

theorem width_16053 : mW 16053 = 524139294660496 := by
  have hu : mW 16053 ≤ 524139294660496 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16053 ≤ 524139294660495 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16053 : RowArithmetic 16053 (268072301939523956821/250000000000000000000000) (588932386752619870901063/1000000000000000000000000) (5126477396168329/1000000000000000000000000) where
  r0 := (1966643689/4000000000000000)
  k0 := (828727247511489/250000000000000000)
  k6 := (10807432535947743/1000000000000000000)
  q := (89590736128240401907/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16053]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16053]

theorem width_16054 : mW 16054 = 524253580487564 := by
  have hu : mW 16054 ≤ 524253580487564 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16054 ≤ 524253580487563 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16054 : RowArithmetic 16054 (1072269308778347075443/1000000000000000000000000) (588923705059240119172359/1000000000000000000000000) (2562824873238379/500000000000000000000000) where
  r0 := (98322996959/200000000000000000)
  k0 := (3314754125145371/1000000000000000000)
  k6 := (2701773983612891/250000000000000000)
  q := (1433496424829863327/8000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16054]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16054]

theorem width_16055 : mW 16055 = 524367884113113 := by
  have hu : mW 16055 ≤ 524367884113113 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16055 ≤ 524367884113112 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16055 : RowArithmetic 16055 (1072249413931576786721/1000000000000000000000000) (147228756104935802451499/250000000000000000000000) (5124822283604653/1000000000000000000000000) where
  r0 := (245784527247/500000000000000000)
  k0 := (3314599277128519/1000000000000000000)
  k6 := (5403379682202081/500000000000000000)
  q := (22399079222146610373/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16055]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16055]

theorem width_16056 : mW 16056 = 524482205538806 := by
  have hu : mW 16056 ≤ 524482205538806 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16056 ≤ 524482205538805 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16056 : RowArithmetic 16056 (1072229523216660785819/1000000000000000000000000) (588906344833924584810961/1000000000000000000000000) (2561997503748933/500000000000000000000000) where
  r0 := (491523131343/1000000000000000000)
  k0 := (1657222222992141/500000000000000000)
  k6 := (10806422825800639/1000000000000000000)
  q := (44799553569204235989/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16056]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16056]

theorem width_16057 : mW 16057 = 524596544766306 := by
  have hu : mW 16057 ≤ 524596544766306 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16057 ≤ 524596544766305 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16057 : RowArithmetic 16057 (1072209636632475288841/1000000000000000000000000) (588897666301579792872733/1000000000000000000000000) (1024633583620453/200000000000000000000000) where
  r0 := (491477215343/1000000000000000000)
  k0 := (662857926343679/200000000000000000)
  k6 := (108060863186361/10000000000000000)
  q := (7168151784107253403/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16057]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16057]

theorem width_16058 : mW 16058 = 524710901797277 := by
  have hu : mW 16058 ≤ 524710901797277 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16058 ≤ 524710901797276 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16058 : RowArithmetic 16058 (268047438544474159909/250000000000000000000000) (18402780900703264512299/31250000000000000000000) (512234101536373/100000000000000000000000) where
  r0 := (491431306491/1000000000000000000)
  k0 := (828533708580777/250000000000000000)
  k6 := (216114996858113/20000000000000000)
  q := (179209374754782290101/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16058]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16058]

theorem width_16059 : mW 16059 = 524825276633381 := by
  have hu : mW 16059 ≤ 524825276633381 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16059 ≤ 524825276633380 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16059 : RowArithmetic 16059 (1072169875851802100279/1000000000000000000000000) (588880312396494212881437/1000000000000000000000000) (256075714961409/50000000000000000000000) where
  r0 := (245692702393/500000000000000000)
  k0 := (3313980053797413/1000000000000000000)
  k6 := (2701353349651099/250000000000000000)
  q := (89607477366568020131/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16059]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16059]

theorem width_16060 : mW 16060 = 524939669276281 := by
  have hu : mW 16060 ≤ 524939669276281 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16060 ≤ 524939669276280 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16060 : RowArithmetic 16060 (26803750041326726501/25000000000000000000000) (588871637023344776218523/1000000000000000000000000) (2560343884820771/500000000000000000000000) where
  r0 := (245669755113/500000000000000000)
  k0 := (3313825290136929/1000000000000000000)
  k6 := (2161015397145489/200000000000000000)
  q := (179220534537758814263/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16060]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16060]

theorem width_16061 : mW 16061 = 525054079727642 := by
  have hu : mW 16061 ≤ 525054079727642 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16061 ≤ 525054079727641 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16061 : RowArithmetic 16061 (1072130131580574772491/1000000000000000000000000) (73607870337856484414461/125000000000000000000000) (1023972285309949/200000000000000000000000) where
  r0 := (491293622809/1000000000000000000)
  k0 := (132546821733491/40000000000000000)
  k6 := (5402370302134953/500000000000000000)
  q := (89613057084333419141/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16061]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16061]

theorem width_16062 : mW 16062 = 525168507989126 := by
  have hu : mW 16062 ≤ 525168507989126 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16062 ≤ 525168507989125 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16062 : RowArithmetic 16062 (214422053126639534363/200000000000000000000000) (588854289434811379038773/1000000000000000000000000) (5119035269898767/1000000000000000000000000) where
  r0 := (98249548507/200000000000000000)
  k0 := (3313515813400813/1000000000000000000)
  k6 := (1350550531778361/125000000000000000)
  q := (5600990425808635499/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16062]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16062]

theorem width_16063 : mW 16063 = 525282954062397 := by
  have hu : mW 16063 ≤ 525282954062397 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16063 ≤ 525282954062396 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16063 : RowArithmetic 16063 (1072090403809816056141/1000000000000000000000000) (294422808609509554188743/500000000000000000000000) (2559104649817293/500000000000000000000000) where
  r0 := (245600934701/500000000000000000)
  k0 := (82834027508079/25000000000000000)
  k6 := (5402033967796751/500000000000000000)
  q := (3584745458188070569/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16063]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16063]

theorem width_16064 : mW 16064 = 525397417949118 := by
  have hu : mW 16064 ≤ 525397417949118 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16064 ≤ 525397417949117 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16064 : RowArithmetic 16064 (67004409131831804817/62500000000000000000000) (147209236513817754007381/250000000000000000000000) (5117383515703207/1000000000000000000000000) where
  r0 := (491156003407/1000000000000000000)
  k0 := (3313206404096559/1000000000000000000)
  k6 := (540186582418243/50000000000000000)
  q := (179242852019264634329/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16064]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16064]

theorem width_16065 : mW 16065 = 525511899650952 := by
  have hu : mW 16065 ≤ 525511899650952 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16065 ≤ 525511899650951 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16065 : RowArithmetic 16065 (1072050692530555476213/1000000000000000000000000) (147207068985840774908137/250000000000000000000000) (5116557918050659/1000000000000000000000000) where
  r0 := (9822202891/20000000000000000)
  k0 := (3313051724723371/1000000000000000000)
  k6 := (5401697696268037/500000000000000000)
  q := (179248430955475869683/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16065]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16065]

theorem width_16066 : mW 16066 = 525626399169564 := by
  have hu : mW 16066 ≤ 525626399169564 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16066 ≤ 525626399169563 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16066 : RowArithmetic 16066 (67001927692027191221/62500000000000000000000) (58881960688309132948933/100000000000000000000000) (2557866253311483/500000000000000000000000) where
  r0 := (491064292829/1000000000000000000)
  k0 := (331289706219921/100000000000000000)
  k6 := (5401529584051129/500000000000000000)
  q := (179254009718053448067/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16066]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16066]

theorem width_16067 : mW 16067 = 525740916506616 := by
  have hu : mW 16067 ≤ 525740916506616 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16067 ≤ 525740916506615 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16067 : RowArithmetic 16067 (268002749433457002831/250000000000000000000000) (588810938874251901646133/1000000000000000000000000) (2557453640683103/500000000000000000000000) where
  r0 := (245509224121/500000000000000000)
  k0 := (414092802064961/125000000000000000)
  k6 := (10802722975058527/1000000000000000000)
  q := (5601862134594174391/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16067]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16067]

theorem width_16068 : mW 16068 = 525855451663773 := by
  have hu : mW 16068 ≤ 525855451663773 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16068 ≤ 525855451663772 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16068 : RowArithmetic 16068 (1071991156513614317341/1000000000000000000000000) (147200567979160211340583/250000000000000000000000) (5114082242226443/1000000000000000000000000) where
  r0 := (122743152697/250000000000000000)
  k0 := (3312587787683793/1000000000000000000)
  k6 := (5401193406699999/500000000000000000)
  q := (179265166722372475527/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16068]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16068]

theorem width_16069 : mW 16069 = 525970004642697 := by
  have hu : mW 16069 ≤ 525970004642697 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16069 ≤ 525970004642696 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16069 : RowArithmetic 16069 (214394263882135028147/200000000000000000000000) (294396803005027217319043/500000000000000000000000) (159789293410931/31250000000000000000000) where
  r0 := (98185356093/200000000000000000)
  k0 := (1656216587843567/500000000000000000)
  k6 := (10802050683121787/1000000000000000000)
  q := (1792707449641463391/10000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16069]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16069]

theorem width_16070 : mW 16070 = 526084575445054 := by
  have hu : mW 16070 ≤ 526084575445054 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16070 ≤ 526084575445053 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16070 : RowArithmetic 16070 (1071951486423890984011/1000000000000000000000000) (147196235288572214721601/250000000000000000000000) (5112432722082349/1000000000000000000000000) where
  r0 := (61360119659/125000000000000000)
  k0 := (1656139290264349/500000000000000000)
  k6 := (2700428646054753/250000000000000000)
  q := (22409540379043921837/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16070]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16070]

theorem width_16071 : mW 16071 = 526199164072506 := by
  have hu : mW 16071 ≤ 526199164072506 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16071 ≤ 526199164072505 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16071 : RowArithmetic 16071 (1071931657552143788771/1000000000000000000000000) (588776277349140493694193/1000000000000000000000000) (2555804120485133/500000000000000000000000) where
  r0 := (245417570603/500000000000000000)
  k0 := (1656062001100359/500000000000000000)
  k6 := (1350172314585849/125000000000000000)
  q := (89640950463501891631/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16071]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16071]

theorem width_16072 : mW 16072 = 526313770526718 := by
  have hu : mW 16072 ≤ 526313770526718 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16072 ≤ 526313770526717 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16072 : RowArithmetic 16072 (1071911832794315098537/1000000000000000000000000) (11775352291888112743001/20000000000000000000000) (5110783945759689/1000000000000000000000000) where
  r0 := (122697333067/250000000000000000)
  k0 := (3311969440708927/1000000000000000000)
  k6 := (1350130310065031/125000000000000000)
  q := (89643739324059881611/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16072]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16072]

theorem width_16073 : mW 16073 = 526428394809353 := by
  have hu : mW 16073 ≤ 526428394809353 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16073 ≤ 526428394809352 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16073 : RowArithmetic 16073 (267973003037321842579/250000000000000000000000) (147189738222470187138209/250000000000000000000000) (798431224437/156250000000000000000) where
  r0 := (98148706091/200000000000000000)
  k0 := (1655907448022779/500000000000000000)
  k6 := (10800706475714501/1000000000000000000)
  q := (89646528097857755241/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16073]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16073]

theorem width_16074 : mW 16074 = 526543036922075 := by
  have hu : mW 16074 ≤ 526543036922075 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16074 ≤ 526543036922074 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16074 : RowArithmetic 16074 (107187219561594318757/100000000000000000000000) (588750292235362271628673/1000000000000000000000000) (5109135912827791/1000000000000000000000000) where
  r0 := (98139547153/200000000000000000)
  k0 := (3311660368206219/1000000000000000000)
  k6 := (5400185251132337/500000000000000000)
  q := (44824658392451804607/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16074]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16074]

theorem width_16075 : mW 16075 = 526657696866549 := by
  have hu : mW 16075 ≤ 526657696866549 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16075 ≤ 526657696866548 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16075 : RowArithmetic 16075 (267963095798291315129/250000000000000000000000) (3679635203941542091327/6250000000000000000000) (2554156087499433/500000000000000000000000) where
  r0 := (490651948197/1000000000000000000)
  k0 := (3311505857189891/1000000000000000000)
  k6 := (10800034560165889/1000000000000000000)
  q := (179304210770411077929/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16075]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16075]

theorem width_16076 : mW 16076 = 526772374644438 := by
  have hu : mW 16076 ≤ 526772374644438 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16076 ≤ 526772374644437 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16076 : RowArithmetic 16076 (1071832574879837211763/1000000000000000000000000) (588732974075530726710839/1000000000000000000000000) (5107488622856267/1000000000000000000000000) where
  r0 := (490606167749/1000000000000000000)
  k0 := (1655675681496089/500000000000000000)
  k6 := (1349962331176659/125000000000000000)
  q := (89654893898771638667/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16076]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16076]

theorem width_16077 : mW 16077 = 526887070257407 := by
  have hu : mW 16077 ≤ 526887070257407 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16077 ≤ 526887070257406 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16077 : RowArithmetic 16077 (1071812770674842528449/1000000000000000000000000) (588724316569810862852999/1000000000000000000000000) (2553332628173117/500000000000000000000000) where
  r0 := (24528019721/50000000000000000)
  k0 := (165559844280603/50000000000000000)
  k6 := (10799362770001947/1000000000000000000)
  q := (44828841162805000619/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16077]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16077]

theorem width_16078 : mW 16078 = 527001783707119 := by
  have hu : mW 16078 ≤ 527001783707119 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16078 ≤ 527001783707118 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16078 : RowArithmetic 16078 (68594750116932199/64000000000000000000) (58871566011328381886159/100000000000000000000000) (638230259426881/125000000000000000000000) where
  r0 := (30657164263/62500000000000000)
  k0 := (165552121252257/50000000000000000)
  k6 := (5399513460963521/500000000000000000)
  q := (17932094133145743667/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16078]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16078]

theorem width_16079 : mW 16079 = 527116514995239 := by
  have hu : mW 16079 ≤ 527116514995239 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16079 ≤ 527116514995238 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16079 : RowArithmetic 16079 (214354634917078143581/200000000000000000000000) (73588375588218294388311/125000000000000000000000) (5105019080008991/1000000000000000000000000) where
  r0 := (490468869113/1000000000000000000)
  k0 := (3310887981293773/1000000000000000000)
  k6 := (2699672776295921/250000000000000000)
  q := (44831629459567940179/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16079]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16079]

theorem width_16080 : mW 16080 = 527231264123431 := by
  have hu : mW 16080 ≤ 527231264123431 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16080 ≤ 527231264123430 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16080 : RowArithmetic 16080 (214350676539740553387/200000000000000000000000) (58869835034699525752853/100000000000000000000000) (5104196270074371/1000000000000000000000000) where
  r0 := (490423117131/1000000000000000000)
  k0 := (3310733554346809/1000000000000000000)
  k6 := (5399177659883501/500000000000000000)
  q := (89666047085839576449/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16080]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16080]

theorem width_16081 : mW 16081 = 527346031093360 := by
  have hu : mW 16081 ≤ 527346031093360 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16081 ≤ 527346031093359 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16081 : RowArithmetic 16081 (535866797457943397819/500000000000000000000000) (58868969703682738640443/100000000000000000000000) (5103373645557509/1000000000000000000000000) where
  r0 := (245188686131/500000000000000000)
  k0 := (16552895721033/5000000000000000)
  k6 := (86384156525377/8000000000000000)
  q := (179337670331695788983/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16081]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16081]

theorem width_16082 : mW 16082 = 527460815906690 := by
  have hu : mW 16082 ≤ 527460815906690 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16082 ≤ 527460815906689 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16082 : RowArithmetic 16082 (1071713811235828492181/1000000000000000000000000) (117736208955007923131409/200000000000000000000000) (5102551206404753/1000000000000000000000000) where
  r0 := (61291454313/125000000000000000)
  k0 := (3310424750868747/1000000000000000000)
  k6 := (2159536768578837/200000000000000000)
  q := (89671623159168921113/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16082]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16082]

theorem width_16083 : mW 16083 = 527575618565084 := by
  have hu : mW 16083 ≤ 527575618565084 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16083 ≤ 527575618565083 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16083 : RowArithmetic 16083 (535847015828707096541/500000000000000000000000) (58867239356142894065537/100000000000000000000000) (5101728952562481/1000000000000000000000000) where
  r0 := (98057180771/200000000000000000)
  k0 := (206891898395553/62500000000000000)
  k6 := (10797348151428313/1000000000000000000)
  q := (35869764426324296673/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16083]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16083]

theorem width_16084 : mW 16084 = 527690439070209 := by
  have hu : mW 16084 ≤ 527690439070209 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16084 ≤ 527690439070208 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16084 : RowArithmetic 16084 (21433485123590591549/20000000000000000000000) (588663743395792349940221/1000000000000000000000000) (5100906883977051/1000000000000000000000000) where
  r0 := (98048036063/200000000000000000)
  k0 := (662023202917851/200000000000000000)
  k6 := (5398506245634821/500000000000000000)
  q := (179354397771562880627/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16084]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16084]

theorem width_16085 : mW 16085 = 527805277423728 := by
  have hu : mW 16085 ≤ 527805277423728 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16085 ≤ 527805277423727 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16085 : RowArithmetic 16085 (267913621200265439031/250000000000000000000000) (588655094277926912006193/1000000000000000000000000) (2550042500297441/500000000000000000000000) where
  r0 := (490194463881/1000000000000000000)
  k0 := (3309961671642189/1000000000000000000)
  k6 := (10796676862413307/1000000000000000000)
  q := (44839993309544549931/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16085]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16085]

theorem width_16086 : mW 16086 = 527920133627305 := by
  have hu : mW 16086 ≤ 527920133627305 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16086 ≤ 527920133627304 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16086 : RowArithmetic 16086 (1674429246126403071/1562500000000000000000) (117729289241525939800017/200000000000000000000000) (2549631651181199/500000000000000000000000) where
  r0 := (61268594319/125000000000000000)
  k0 := (3309807345486623/1000000000000000000)
  k6 := (5398170632427221/500000000000000000)
  q := (179365548531483603857/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16086]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16086]

theorem width_16087 : mW 16087 = 528035007682606 := by
  have hu : mW 16087 ≤ 528035007682606 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16087 ≤ 528035007682605 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16087 : RowArithmetic 16087 (535807477168962653397/500000000000000000000000) (73579724898087242808909/125000000000000000000000) (5098441789226027/1000000000000000000000000) where
  r0 := (245051526163/500000000000000000)
  k0 := (413706629514769/125000000000000000)
  k6 := (1349500712323523/125000000000000000)
  q := (89685561825747626857/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16087]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16087]

theorem width_16088 : mW 16088 = 528149899591295 := by
  have hu : mW 16088 ≤ 528149899591295 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16088 ≤ 528149899591294 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16088 : RowArithmetic 16088 (107159519525103178999/100000000000000000000000) (147157288302232207274993/250000000000000000000000) (2548810230566117/500000000000000000000000) where
  r0 := (245028678601/500000000000000000)
  k0 := (3309498743535749/1000000000000000000)
  k6 := (10795670163609669/1000000000000000000)
  q := (11211043662389331717/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16088]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16088]

theorem width_16089 : mW 16089 = 528264809355037 := by
  have hu : mW 16089 ≤ 528264809355037 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16089 ≤ 528264809355036 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16089 : RowArithmetic 16089 (267893860064776387617/250000000000000000000000) (588620508280119691523791/1000000000000000000000000) (2548399659013747/500000000000000000000000) where
  r0 := (245005834589/500000000000000000)
  k0 := (103417014616719/31250000000000000)
  k6 := (10795334659914037/1000000000000000000)
  q := (179382273371701920797/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16089]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16089]

theorem width_16090 : mW 16090 = 528379736975496 := by
  have hu : mW 16090 ≤ 528379736975496 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16090 ≤ 528379736975495 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16090 : RowArithmetic 16090 (1071555689361035370521/1000000000000000000000000) (588611864398067822019997/1000000000000000000000000) (5095978359858311/1000000000000000000000000) where
  r0 := (489965988253/1000000000000000000)
  k0 := (1654595104357449/500000000000000000)
  k6 := (5397499593748213/500000000000000000)
  q := (35877569594385849369/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16090]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16090]

theorem width_16091 : mW 16091 = 528494682454338 := by
  have hu : mW 16091 ≤ 528494682454338 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16091 ≤ 528494682454337 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16091 : RowArithmetic 16091 (1071535942555709897557/1000000000000000000000000) (73575402695321325182089/125000000000000000000000) (509515758657119/100000000000000000000000) where
  r0 := (244960157213/500000000000000000)
  k0 := (330903596647439/100000000000000000)
  k6 := (1349332968293997/125000000000000000)
  q := (179393422398927436261/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16091]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16091]

theorem width_16092 : mW 16092 = 528609645793227 := by
  have hu : mW 16092 ≤ 528609645793227 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16092 ≤ 528609645793226 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16092 : RowArithmetic 16092 (535758099921009342971/500000000000000000000000) (588594579773425509980719/1000000000000000000000000) (5094336998112673/1000000000000000000000000) where
  r0 := (489874647693/1000000000000000000)
  k0 := (3308881741002321/1000000000000000000)
  k6 := (1079432833647583/100000000000000000)
  q := (179398996652712637183/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16092]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16092]

theorem width_16093 : mW 16093 = 528724626993829 := by
  have hu : mW 16093 ≤ 528724626993829 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16093 ≤ 528724626993828 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16093 : RowArithmetic 16093 (107149646121885115519/100000000000000000000000) (4708687512243439897289/8000000000000000000000) (636689574303663/125000000000000000000000) where
  r0 := (97965797611/200000000000000000)
  k0 := (3308727532304413/1000000000000000000)
  k6 := (10793992957863129/1000000000000000000)
  q := (89702285366650497619/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16093]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16093]

theorem width_16094 : mW 16094 = 528839626057807 := by
  have hu : mW 16094 ≤ 528839626057807 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16094 ≤ 528839626057806 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16094 : RowArithmetic 16094 (535738363342548945567/500000000000000000000000) (147144324833345406816279/250000000000000000000000) (5092696375467673/1000000000000000000000000) where
  r0 := (48978333551/100000000000000000)
  k0 := (3308573340376257/1000000000000000000)
  k6 := (10793657610509017/1000000000000000000)
  q := (179410144640708653547/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16094]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16094]

theorem width_16095 : mW 16095 = 528954642986828 := by
  have hu : mW 16095 ≤ 528954642986828 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16095 ≤ 528954642986827 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16095 : RowArithmetic 16095 (1071456996239648824429/1000000000000000000000000) (294284330341039017148331/500000000000000000000000) (2545938170587177/500000000000000000000000) where
  r0 := (97947538011/200000000000000000)
  k0 := (3308419165210063/1000000000000000000)
  k6 := (10793322294408639/1000000000000000000)
  q := (179415718374951752721/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16095]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16095]

theorem width_16096 : mW 16096 = 529069677782557 := by
  have hu : mW 16096 ≤ 529069677782557 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16096 ≤ 529069677782556 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16096 : RowArithmetic 16096 (535718634940697395811/500000000000000000000000) (117712004615263368976329/200000000000000000000000) (1272764122873989/250000000000000000000000) where
  r0 := (48969205169/100000000000000000)
  k0 := (206766562925511/62500000000000000)
  k6 := (10792987009557141/1000000000000000000)
  q := (89710645968023215433/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16096]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16096]

theorem width_16097 : mW 16097 = 529184730446658 := by
  have hu : mW 16097 ≤ 529184730446658 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16097 ≤ 529184730446657 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16097 : RowArithmetic 16097 (1071417547609227274239/1000000000000000000000000) (36784461657243485803141/62500000000000000000000) (5090236826379119/1000000000000000000000000) where
  r0 := (489646420413/1000000000000000000)
  k0 := (3308110865166183/1000000000000000000)
  k6 := (10792651755949669/1000000000000000000)
  q := (89713432662004411791/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16097]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16097]

theorem width_16098 : mW 16098 = 529299800980796 := by
  have hu : mW 16098 ≤ 529299800980796 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16098 ≤ 529299800980795 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16098 : RowArithmetic 16098 (1071397829422037878731/1000000000000000000000000) (11770855020012251943619/20000000000000000000000) (5089417345770493/1000000000000000000000000) where
  r0 := (244800398111/500000000000000000)
  k0 := (330795674027967/100000000000000000)
  k6 := (1079231653358137/100000000000000000)
  q := (4485810963471376599/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16098]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16098]

theorem width_16099 : mW 16099 = 529414889386638 := by
  have hu : mW 16099 ≤ 529414889386638 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16099 ≤ 529414889386637 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16099 : RowArithmetic 16099 (1071378115318718077157/1000000000000000000000000) (147133529132566275434681/250000000000000000000000) (636074756202091/125000000000000000000000) where
  r0 := (122388794779/250000000000000000)
  k0 := (1653901316073801/500000000000000000)
  k6 := (5395990671223697/500000000000000000)
  q := (179438011580601282587/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16099]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16099]

theorem width_16100 : mW 16100 = 529529995665848 := by
  have hu : mW 16100 ≤ 529529995665848 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16100 ≤ 529529995665847 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16100 : RowArithmetic 16100 (1071358405298160505543/1000000000000000000000000) (294262741552325595795721/500000000000000000000000) (127194473446613/25000000000000000000000) where
  r0 := (489509569093/1000000000000000000)
  k0 := (1653824270382781/500000000000000000)
  k6 := (10791646182542891/1000000000000000000)
  q := (44860896112315901887/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16100]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16100]

theorem width_16101 : mW 16101 = 529645119820091 := by
  have hu : mW 16101 ≤ 529645119820091 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16101 ≤ 529645119820090 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16101 : RowArithmetic 16101 (267834674839814481151/250000000000000000000000) (14712921268089219824627/25000000000000000000000) (5086960010460577/1000000000000000000000000) where
  r0 := (61182995769/125000000000000000)
  k0 := (1653747233066257/500000000000000000)
  k6 := (2697827763465753/250000000000000000)
  q := (179449157144858164419/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16101]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16101]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 16027 then ⟨(107280803559880690789/100000000000000000000000), (589158481364631722635027/1000000000000000000000000), (1029612407926963/200000000000000000000000)⟩ else
  if n = 16028 then ⟨(1072788028765789931153/1000000000000000000000000), (589149772198336772675323/1000000000000000000000000), (2573614756783681/500000000000000000000000)⟩ else
  if n = 16029 then ⟨(1072768026095113380927/1000000000000000000000000), (589141064091261103843289/1000000000000000000000000), (2573198587867023/500000000000000000000000)⟩ else
  if n = 16030 then ⟨(1072748027585642848057/1000000000000000000000000), (589132357043198802582531/1000000000000000000000000), (25727825130401/5000000000000000000000)⟩ else
  if n = 16031 then ⟨(1072728033236244851573/1000000000000000000000000), (3682022819087149809153/6250000000000000000000), (5144733064551201/1000000000000000000000000)⟩ else
  if n = 16032 then ⟨(268177010761446509897/250000000000000000000000), (294557473061645367684809/500000000000000000000000), (5143901291092433/1000000000000000000000000)⟩ else
  if n = 16033 then ⟨(214537611402626744277/200000000000000000000000), (117821248450206679108581/200000000000000000000000), (5143069705649311/1000000000000000000000000)⟩ else
  if n = 16034 then ⟨(1072668075137155069377/1000000000000000000000000), (589097539436966228458373/1000000000000000000000000), (5142238308167251/1000000000000000000000000)⟩ else
  if n = 16035 then ⟨(1072648097416717916981/1000000000000000000000000), (589088837680883548799589/1000000000000000000000000), (5141407098591697/1000000000000000000000000)⟩ else
  if n = 16036 then ⟨(268157030962672689489/250000000000000000000000), (73635017122822468590187/125000000000000000000000), (5140576076868123/1000000000000000000000000)⟩ else
  if n = 16037 then ⟨(26815203860948548731/25000000000000000000000), (117814287468369856916517/200000000000000000000000), (5139745242942003/1000000000000000000000000)⟩ else
  if n = 16038 then ⟨(134073523647167596669/125000000000000000000000), (589062738758486660644693/1000000000000000000000000), (5138914596758853/1000000000000000000000000)⟩ else
  if n = 16039 then ⟨(1072568228067756376021/1000000000000000000000000), (368158775770179038533/625000000000000000000), (2569042069132093/500000000000000000000000)⟩ else
  if n = 16040 then ⟨(536274135554029281303/500000000000000000000000), (73630668095380409309407/125000000000000000000000), (2568626933701773/500000000000000000000000)⟩ else
  if n = 16041 then ⟨(536264159148558633603/500000000000000000000000), (589036649350551772514413/1000000000000000000000000), (2568211892061243/500000000000000000000000)⟩ else
  if n = 16042 then ⟨(13406354620422545163/12500000000000000000000), (294513977497303345804539/500000000000000000000000), (513559388836661/100000000000000000000000)⟩ else
  if n = 16043 then ⟨(1072488425116987791441/1000000000000000000000000), (589019261695002768526281/1000000000000000000000000), (1283691045020373/250000000000000000000000)⟩ else
  if n = 16044 then ⟨(134058560593192680941/125000000000000000000000), (294505284725767452913789/500000000000000000000000), (1283483664803191/250000000000000000000000)⟩ else
  if n = 16045 then ⟨(536224274259168044859/500000000000000000000000), (589001878263997955198781/1000000000000000000000000), (5133105325706059/1000000000000000000000000)⟩ else
  if n = 16046 then ⟨(1072428616434243884417/1000000000000000000000000), (36812074258261677316917/62500000000000000000000), (32076726121919/6250000000000000000000)⟩ else
  if n = 16047 then ⟨(1072408688492137390823/1000000000000000000000000), (588984499055896616750713/1000000000000000000000000), (1282861805140347/250000000000000000000000)⟩ else
  if n = 16048 then ⟨(1072388764690889031857/1000000000000000000000000), (147243952758730564737967/250000000000000000000000), (5130618448814787/1000000000000000000000000)⟩ else
  if n = 16049 then ⟨(214473769005874430469/200000000000000000000000), (588967124069058951418531/1000000000000000000000000), (2564894932106479/500000000000000000000000)⟩ else
  if n = 16050 then ⟨(536174464753230112559/500000000000000000000000), (588958438158101811993813/1000000000000000000000000), (5128961466701633/1000000000000000000000000)⟩ else
  if n = 16051 then ⟨(536164509060513689817/500000000000000000000000), (294474876650923014316567/500000000000000000000000), (1282033314056643/250000000000000000000000)⟩ else
  if n = 16052 then ⟨(1072309110871947609133/1000000000000000000000000), (294470534750043468499781/500000000000000000000000), (5127305232733537/1000000000000000000000000)⟩ else
  if n = 16053 then ⟨(268072301939523956821/250000000000000000000000), (588932386752619870901063/1000000000000000000000000), (5126477396168329/1000000000000000000000000)⟩ else
  if n = 16054 then ⟨(1072269308778347075443/1000000000000000000000000), (588923705059240119172359/1000000000000000000000000), (2562824873238379/500000000000000000000000)⟩ else
  if n = 16055 then ⟨(1072249413931576786721/1000000000000000000000000), (147228756104935802451499/250000000000000000000000), (5124822283604653/1000000000000000000000000)⟩ else
  if n = 16056 then ⟨(1072229523216660785819/1000000000000000000000000), (588906344833924584810961/1000000000000000000000000), (2561997503748933/500000000000000000000000)⟩ else
  if n = 16057 then ⟨(1072209636632475288841/1000000000000000000000000), (588897666301579792872733/1000000000000000000000000), (1024633583620453/200000000000000000000000)⟩ else
  if n = 16058 then ⟨(268047438544474159909/250000000000000000000000), (18402780900703264512299/31250000000000000000000), (512234101536373/100000000000000000000000)⟩ else
  if n = 16059 then ⟨(1072169875851802100279/1000000000000000000000000), (588880312396494212881437/1000000000000000000000000), (256075714961409/50000000000000000000000)⟩ else
  if n = 16060 then ⟨(26803750041326726501/25000000000000000000000), (588871637023344776218523/1000000000000000000000000), (2560343884820771/500000000000000000000000)⟩ else
  if n = 16061 then ⟨(1072130131580574772491/1000000000000000000000000), (73607870337856484414461/125000000000000000000000), (1023972285309949/200000000000000000000000)⟩ else
  if n = 16062 then ⟨(214422053126639534363/200000000000000000000000), (588854289434811379038773/1000000000000000000000000), (5119035269898767/1000000000000000000000000)⟩ else
  if n = 16063 then ⟨(1072090403809816056141/1000000000000000000000000), (294422808609509554188743/500000000000000000000000), (2559104649817293/500000000000000000000000)⟩ else
  if n = 16064 then ⟨(67004409131831804817/62500000000000000000000), (147209236513817754007381/250000000000000000000000), (5117383515703207/1000000000000000000000000)⟩ else
  if n = 16065 then ⟨(1072050692530555476213/1000000000000000000000000), (147207068985840774908137/250000000000000000000000), (5116557918050659/1000000000000000000000000)⟩ else
  if n = 16066 then ⟨(67001927692027191221/62500000000000000000000), (58881960688309132948933/100000000000000000000000), (2557866253311483/500000000000000000000000)⟩ else
  if n = 16067 then ⟨(268002749433457002831/250000000000000000000000), (588810938874251901646133/1000000000000000000000000), (2557453640683103/500000000000000000000000)⟩ else
  if n = 16068 then ⟨(1071991156513614317341/1000000000000000000000000), (147200567979160211340583/250000000000000000000000), (5114082242226443/1000000000000000000000000)⟩ else
  if n = 16069 then ⟨(214394263882135028147/200000000000000000000000), (294396803005027217319043/500000000000000000000000), (159789293410931/31250000000000000000000)⟩ else
  if n = 16070 then ⟨(1071951486423890984011/1000000000000000000000000), (147196235288572214721601/250000000000000000000000), (5112432722082349/1000000000000000000000000)⟩ else
  if n = 16071 then ⟨(1071931657552143788771/1000000000000000000000000), (588776277349140493694193/1000000000000000000000000), (2555804120485133/500000000000000000000000)⟩ else
  if n = 16072 then ⟨(1071911832794315098537/1000000000000000000000000), (11775352291888112743001/20000000000000000000000), (5110783945759689/1000000000000000000000000)⟩ else
  if n = 16073 then ⟨(267973003037321842579/250000000000000000000000), (147189738222470187138209/250000000000000000000000), (798431224437/156250000000000000000)⟩ else
  if n = 16074 then ⟨(107187219561594318757/100000000000000000000000), (588750292235362271628673/1000000000000000000000000), (5109135912827791/1000000000000000000000000)⟩ else
  if n = 16075 then ⟨(267963095798291315129/250000000000000000000000), (3679635203941542091327/6250000000000000000000), (2554156087499433/500000000000000000000000)⟩ else
  if n = 16076 then ⟨(1071832574879837211763/1000000000000000000000000), (588732974075530726710839/1000000000000000000000000), (5107488622856267/1000000000000000000000000)⟩ else
  if n = 16077 then ⟨(1071812770674842528449/1000000000000000000000000), (588724316569810862852999/1000000000000000000000000), (2553332628173117/500000000000000000000000)⟩ else
  if n = 16078 then ⟨(68594750116932199/64000000000000000000), (58871566011328381886159/100000000000000000000000), (638230259426881/125000000000000000000000)⟩ else
  if n = 16079 then ⟨(214354634917078143581/200000000000000000000000), (73588375588218294388311/125000000000000000000000), (5105019080008991/1000000000000000000000000)⟩ else
  if n = 16080 then ⟨(214350676539740553387/200000000000000000000000), (58869835034699525752853/100000000000000000000000), (5104196270074371/1000000000000000000000000)⟩ else
  if n = 16081 then ⟨(535866797457943397819/500000000000000000000000), (58868969703682738640443/100000000000000000000000), (5103373645557509/1000000000000000000000000)⟩ else
  if n = 16082 then ⟨(1071713811235828492181/1000000000000000000000000), (117736208955007923131409/200000000000000000000000), (5102551206404753/1000000000000000000000000)⟩ else
  if n = 16083 then ⟨(535847015828707096541/500000000000000000000000), (58867239356142894065537/100000000000000000000000), (5101728952562481/1000000000000000000000000)⟩ else
  if n = 16084 then ⟨(21433485123590591549/20000000000000000000000), (588663743395792349940221/1000000000000000000000000), (5100906883977051/1000000000000000000000000)⟩ else
  if n = 16085 then ⟨(267913621200265439031/250000000000000000000000), (588655094277926912006193/1000000000000000000000000), (2550042500297441/500000000000000000000000)⟩ else
  if n = 16086 then ⟨(1674429246126403071/1562500000000000000000), (117729289241525939800017/200000000000000000000000), (2549631651181199/500000000000000000000000)⟩ else
  if n = 16087 then ⟨(535807477168962653397/500000000000000000000000), (73579724898087242808909/125000000000000000000000), (5098441789226027/1000000000000000000000000)⟩ else
  if n = 16088 then ⟨(107159519525103178999/100000000000000000000000), (147157288302232207274993/250000000000000000000000), (2548810230566117/500000000000000000000000)⟩ else
  if n = 16089 then ⟨(267893860064776387617/250000000000000000000000), (588620508280119691523791/1000000000000000000000000), (2548399659013747/500000000000000000000000)⟩ else
  if n = 16090 then ⟨(1071555689361035370521/1000000000000000000000000), (588611864398067822019997/1000000000000000000000000), (5095978359858311/1000000000000000000000000)⟩ else
  if n = 16091 then ⟨(1071535942555709897557/1000000000000000000000000), (73575402695321325182089/125000000000000000000000), (509515758657119/100000000000000000000000)⟩ else
  if n = 16092 then ⟨(535758099921009342971/500000000000000000000000), (588594579773425509980719/1000000000000000000000000), (5094336998112673/1000000000000000000000000)⟩ else
  if n = 16093 then ⟨(107149646121885115519/100000000000000000000000), (4708687512243439897289/8000000000000000000000), (636689574303663/125000000000000000000000)⟩ else
  if n = 16094 then ⟨(535738363342548945567/500000000000000000000000), (147144324833345406816279/250000000000000000000000), (5092696375467673/1000000000000000000000000)⟩ else
  if n = 16095 then ⟨(1071456996239648824429/1000000000000000000000000), (294284330341039017148331/500000000000000000000000), (2545938170587177/500000000000000000000000)⟩ else
  if n = 16096 then ⟨(535718634940697395811/500000000000000000000000), (117712004615263368976329/200000000000000000000000), (1272764122873989/250000000000000000000000)⟩ else
  if n = 16097 then ⟨(1071417547609227274239/1000000000000000000000000), (36784461657243485803141/62500000000000000000000), (5090236826379119/1000000000000000000000000)⟩ else
  if n = 16098 then ⟨(1071397829422037878731/1000000000000000000000000), (11770855020012251943619/20000000000000000000000), (5089417345770493/1000000000000000000000000)⟩ else
  if n = 16099 then ⟨(1071378115318718077157/1000000000000000000000000), (147133529132566275434681/250000000000000000000000), (636074756202091/125000000000000000000000)⟩ else
  if n = 16100 then ⟨(1071358405298160505543/1000000000000000000000000), (294262741552325595795721/500000000000000000000000), (127194473446613/25000000000000000000000)⟩ else
  ⟨(267834674839814481151/250000000000000000000000), (14712921268089219824627/25000000000000000000000), (5086960010460577/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 16027 ≤ n) (hb : n ≤ 16101) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_16027
  · exact row_16028
  · exact row_16029
  · exact row_16030
  · exact row_16031
  · exact row_16032
  · exact row_16033
  · exact row_16034
  · exact row_16035
  · exact row_16036
  · exact row_16037
  · exact row_16038
  · exact row_16039
  · exact row_16040
  · exact row_16041
  · exact row_16042
  · exact row_16043
  · exact row_16044
  · exact row_16045
  · exact row_16046
  · exact row_16047
  · exact row_16048
  · exact row_16049
  · exact row_16050
  · exact row_16051
  · exact row_16052
  · exact row_16053
  · exact row_16054
  · exact row_16055
  · exact row_16056
  · exact row_16057
  · exact row_16058
  · exact row_16059
  · exact row_16060
  · exact row_16061
  · exact row_16062
  · exact row_16063
  · exact row_16064
  · exact row_16065
  · exact row_16066
  · exact row_16067
  · exact row_16068
  · exact row_16069
  · exact row_16070
  · exact row_16071
  · exact row_16072
  · exact row_16073
  · exact row_16074
  · exact row_16075
  · exact row_16076
  · exact row_16077
  · exact row_16078
  · exact row_16079
  · exact row_16080
  · exact row_16081
  · exact row_16082
  · exact row_16083
  · exact row_16084
  · exact row_16085
  · exact row_16086
  · exact row_16087
  · exact row_16088
  · exact row_16089
  · exact row_16090
  · exact row_16091
  · exact row_16092
  · exact row_16093
  · exact row_16094
  · exact row_16095
  · exact row_16096
  · exact row_16097
  · exact row_16098
  · exact row_16099
  · exact row_16100
  · exact row_16101

end BstLean.Part271.R3.Rows16027
