import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14885–14959. -/
namespace BstLean.Part271.R3.Rows14885
open Real BstLean.Part130 BstLean.Part227

theorem width_14885 : mW 14885 = 402365685741002 := by
  have hu : mW 14885 ≤ 402365685741002 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14885 ≤ 402365685741001 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14885 : RowArithmetic 14885 (68667786175842178633/62500000000000000000000) (599851155269097255950119/1000000000000000000000000) (3118392839964409/500000000000000000000000) where
  r0 := (275325696067/500000000000000000)
  k0 := (175407088042323/50000000000000000)
  k6 := (448937835018523/40000000000000000)
  q := (43134962617347890777/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14885]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14885]

theorem width_14886 : mW 14886 = 402460304361588 := by
  have hu : mW 14886 ≤ 402460304361588 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14886 ≤ 402460304361587 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14886 : RowArithmetic 14886 (68666185703519715631/62500000000000000000000) (599841086909126628019371/1000000000000000000000000) (6235697052445529/1000000000000000000000000) where
  r0 := (550595906227/1000000000000000000)
  k0 := (1753982504486109/500000000000000000)
  k6 := (5611534444610959/500000000000000000)
  q := (172545646134580863263/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14886]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14886]

theorem width_14887 : mW 14887 = 402554938874045 := by
  have hu : mW 14887 ≤ 402554938874045 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14887 ≤ 402554938874044 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14887 : RowArithmetic 14887 (219726673889906723473/200000000000000000000000) (599831019884720777949019/1000000000000000000000000) (6234608690585853/1000000000000000000000000) where
  r0 := (550540429637/1000000000000000000)
  k0 := (3507788277873531/1000000000000000000)
  k6 := (5611345970483087/500000000000000000)
  q := (172551441605105113651/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14887]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14887]

theorem width_14888 : mW 14888 = 402649589279977 := by
  have hu : mW 14888 ≤ 402649589279977 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14888 ≤ 402649589279976 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14888 : RowArithmetic 14888 (1098607773391437720911/1000000000000000000000000) (599820954195596525072899/1000000000000000000000000) (6233520594266539/1000000000000000000000000) where
  r0 := (550484962363/1000000000000000000)
  k0 := (1753805783775177/500000000000000000)
  k6 := (5611157515344733/500000000000000000)
  q := (10784827305061495513/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14888]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14888]

theorem width_14889 : mW 14889 = 402744255580984 := by
  have hu : mW 14889 ≤ 402744255580984 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14889 ≤ 402744255580983 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14889 : RowArithmetic 14889 (549291091540169197653/500000000000000000000000) (299905444920735403018481/500000000000000000000000) (1558108190851107/250000000000000000000000) where
  r0 := (275214752201/500000000000000000)
  k0 := (3507434877996269/1000000000000000000)
  k6 := (2244387631677083/200000000000000000)
  q := (172563031962236917577/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14889]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14889]

theorem width_14890 : mW 14890 = 402838937778668 := by
  have hu : mW 14890 ≤ 402838937778668 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14890 ≤ 402838937778667 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14890 : RowArithmetic 14890 (274639149628636523057/250000000000000000000000) (599800826822060595067291/1000000000000000000000000) (1557836299479091/250000000000000000000000) where
  r0 := (68796756969/125000000000000000)
  k0 := (1753629104604021/500000000000000000)
  k6 := (350673791376489/31250000000000000)
  q := (172568826848883689107/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14890]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14890]

theorem width_14891 : mW 14891 = 402933635874631 := by
  have hu : mW 14891 ≤ 402933635874631 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14891 ≤ 402933635874630 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14891 : RowArithmetic 14891 (274632754923092974773/250000000000000000000000) (299895382568541535435653/500000000000000000000000) (778782237214903/125000000000000000000000) where
  r0 := (137579654103/250000000000000000)
  k0 := (5611330497897/1600000000000000)
  k6 := (11221184527669789/1000000000000000000)
  q := (86287310770471923429/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14891]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14891]

theorem width_14892 : mW 14892 = 403028349870474 := by
  have hu : mW 14892 ≤ 403028349870474 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14892 ≤ 403028349870473 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14892 : RowArithmetic 14892 (1098505446612127947249/1000000000000000000000000) (74972588098281914608077/125000000000000000000000) (622917086272993/100000000000000000000000) where
  r0 := (275131593189/500000000000000000)
  k0 := (350690493391941/100000000000000000)
  k6 := (2244161553849093/200000000000000000)
  q := (43145104009609247899/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14892]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14892]

theorem width_14893 : mW 14893 = 403123079767798 := by
  have hu : mW 14893 ≤ 403123079767798 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14893 ≤ 403123079767797 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14893 : RowArithmetic 14893 (1098479879272127002533/1000000000000000000000000) (599770645769294647532037/1000000000000000000000000) (6228084092865441/1000000000000000000000000) where
  r0 := (34387985353/62500000000000000)
  k0 := (43834104092577/12500000000000000)
  k6 := (11220431048768307/1000000000000000000)
  q := (172586210341382720797/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14893]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14893]

theorem width_14894 : mW 14894 = 403217825568206 := by
  have hu : mW 14894 ≤ 403217825568206 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14894 ≤ 403217825568205 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14894 : RowArithmetic 14894 (549227158835340824281/500000000000000000000000) (119952117617183677665471/200000000000000000000000) (1245399517608543/200000000000000000000000) where
  r0 := (550152354221/1000000000000000000)
  k0 := (3506551741645823/1000000000000000000)
  k6 := (11220054366231943/1000000000000000000)
  q := (172592004449800628649/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14894]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14894]

theorem width_14895 : mW 14895 = 403312587273299 := by
  have hu : mW 14895 ≤ 403312587273299 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14895 ≤ 403312587273298 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14895 : RowArithmetic 14895 (549214380903052960081/500000000000000000000000) (299875265867921958456231/500000000000000000000000) (3112955674089387/500000000000000000000000) where
  r0 := (275048476047/500000000000000000)
  k0 := (1753187588315987/500000000000000000)
  k6 := (11219677721630007/1000000000000000000)
  q := (172597798363710306049/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14895]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14895]

theorem width_14896 : mW 14896 = 403407364884679 := by
  have hu : mW 14896 ≤ 403407364884679 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14896 ≤ 403407364884678 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14896 : RowArithmetic 14896 (1098403211676714077837/1000000000000000000000000) (599740476718788827390593/1000000000000000000000000) (6224825373190657/1000000000000000000000000) where
  r0 := (110008311853/200000000000000000)
  k0 := (876549658090343/250000000000000000)
  k6 := (1121930111495613/100000000000000000)
  q := (2696931126298927197/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14896]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14896]

theorem width_14897 : mW 14897 = 403502158403948 := by
  have hu : mW 14897 ≤ 403502158403948 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14897 ≤ 403502158403947 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14897 : RowArithmetic 14897 (1098377667280821015981/1000000000000000000000000) (599730423034470628652913/1000000000000000000000000) (1555934915748859/250000000000000000000000) where
  r0 := (137496543933/250000000000000000)
  k0 := (438252763603847/125000000000000000)
  k6 := (11218924546203949/1000000000000000000)
  q := (172609385608083316647/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14897]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14897]

theorem width_14898 : mW 14898 = 403596967832708 := by
  have hu : mW 14898 ≤ 403596967832708 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14898 ≤ 403596967832707 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14898 : RowArithmetic 14898 (1098352128616742262561/1000000000000000000000000) (599720370682607045912821/1000000000000000000000000) (1244530843502043/200000000000000000000000) where
  r0 := (549930801493/1000000000000000000)
  k0 := (701169121207389/200000000000000000)
  k6 := (11218548015367099/1000000000000000000)
  q := (172615178938585815203/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14898]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14898]

theorem width_14899 : mW 14899 = 403691793172560 := by
  have hu : mW 14899 ≤ 403691793172560 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14899 ≤ 403691793172559 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14899 : RowArithmetic 14899 (1098326595682794386209/1000000000000000000000000) (599710319662915768012707/1000000000000000000000000) (3110784518326073/500000000000000000000000) where
  r0 := (109975087309/200000000000000000)
  k0 := (3505669123973447/1000000000000000000)
  k6 := (5609085761219609/500000000000000000)
  q := (172620972074658414027/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14899]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14899]

theorem width_14900 : mW 14900 = 403786634425107 := by
  have hu : mW 14900 ≤ 403786634425107 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14900 ≤ 403786634425106 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14900 : RowArithmetic 14900 (274575267119323443353/250000000000000000000000) (599700269975114694058213/1000000000000000000000000) (6220484120338383/1000000000000000000000000) where
  r0 := (274910040443/500000000000000000)
  k0 := (3505492662637037/1000000000000000000)
  k6 := (5608897533706973/500000000000000000)
  q := (172626765016320687583/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14900]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14900]

theorem width_14901 : mW 14901 = 403881491591952 := by
  have hu : mW 14901 ≤ 403881491591952 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14901 ≤ 403881491591951 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14901 : RowArithmetic 14901 (219655109399711488789/200000000000000000000000) (599690221618921708964709/1000000000000000000000000) (6219399468486113/1000000000000000000000000) where
  r0 := (274882367257/500000000000000000)
  k0 := (350531622202447/100000000000000000)
  k6 := (11217418650284923/1000000000000000000)
  q := (172632557763592207051/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14901]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14901]

theorem width_14902 : mW 14902 = 403976364674695 := by
  have hu : mW 14902 ≤ 403976364674695 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14902 ≤ 403976364674694 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14902 : RowArithmetic 14902 (549125015622452135661/500000000000000000000000) (599680174594054801559783/1000000000000000000000000) (6218315081012599/1000000000000000000000000) where
  r0 := (549709397427/1000000000000000000)
  k0 := (3505139802132499/1000000000000000000)
  k6 := (350532570970181/31250000000000000)
  q := (172638350316492540331/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14902]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14902]

theorem width_14903 : mW 14903 = 404071253674939 := by
  have hu : mW 14903 ≤ 404071253674939 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14903 ≤ 404071253674938 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14903 : RowArithmetic 14903 (549112260607326269773/500000000000000000000000) (149917532225058003997619/250000000000000000000000) (3108615478917547/500000000000000000000000) where
  r0 := (549654069623/1000000000000000000)
  k0 := (876240850739469/250000000000000000)
  k6 := (11216665929690197/1000000000000000000)
  q := (34528828535008250407/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14903]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14903]

theorem width_14904 : mW 14904 = 404166158594287 := by
  have hu : mW 14904 ≤ 404166158594287 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14904 ≤ 404166158594286 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14904 : RowArithmetic 14904 (1098199016906121164989/1000000000000000000000000) (59966008453717158135189/100000000000000000000000) (38850919367943/6250000000000000000000) where
  r0 := (5495987511/10000000000000000)
  k0 := (438098378062169/125000000000000000)
  k6 := (5608144813105891/500000000000000000)
  q := (86324967419628951749/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14904]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14904]

theorem width_14905 : mW 14905 = 404261079434341 := by
  have hu : mW 14905 ≤ 404261079434341 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14905 ≤ 404261079434340 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14905 : RowArithmetic 14905 (549086759158815051263/500000000000000000000000) (119930008300918342500729/200000000000000000000000) (621506350403729/100000000000000000000000) where
  r0 := (109908688371/200000000000000000)
  k0 := (3504610666744489/1000000000000000000)
  k6 := (2243182672120839/200000000000000000)
  q := (17265572680916205277/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14905]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14905]

theorem width_14906 : mW 14906 = 404356016196702 := by
  have hu : mW 14906 ≤ 404356016196702 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14906 ≤ 404356016196701 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14906 : RowArithmetic 14906 (549074012723750172217/500000000000000000000000) (11992799996044214684991/20000000000000000000000) (6213980173251703/1000000000000000000000000) where
  r0 := (274744070943/500000000000000000)
  k0 := (876108582424009/250000000000000000)
  k6 := (2803884283215271/250000000000000000)
  q := (5395672455774164207/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14906]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14906]

theorem width_14907 : mW 14907 = 404450968882975 := by
  have hu : mW 14907 ≤ 404450968882975 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14907 ≤ 404450968882974 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14907 : RowArithmetic 14907 (1098122538294051888671/1000000000000000000000000) (149907489857436768770347/250000000000000000000000) (1553224276607867/250000000000000000000000) where
  r0 := (549432851191/1000000000000000000)
  k0 := (3504258013348739/1000000000000000000)
  k6 := (5607580471488049/500000000000000000)
  q := (172667310166111060549/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14907]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14907]

theorem width_14908 : mW 14908 = 404545937494760 := by
  have hu : mW 14908 ≤ 404545937494760 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14908 ≤ 404545937494759 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14908 : RowArithmetic 14908 (549048528427803697717/500000000000000000000000) (149904980096729798412937/250000000000000000000000) (1242362860698809/200000000000000000000000) where
  r0 := (68672196221/125000000000000000)
  k0 := (3504081717699347/1000000000000000000)
  k6 := (1121478479094289/100000000000000000)
  q := (4316827538829875469/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14908]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14908]

theorem width_14909 : mW 14909 = 404640922033661 := by
  have hu : mW 14909 ≤ 404640922033661 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14909 ≤ 404640922033660 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14909 : RowArithmetic 14909 (1098071581130488530623/1000000000000000000000000) (149902470668361413823661/250000000000000000000000) (1242146352871373/200000000000000000000000) where
  r0 := (274661148807/500000000000000000)
  k0 := (1751952721370707/500000000000000000)
  k6 := (11214408676755111/1000000000000000000)
  q := (172678892746044674191/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14909]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14909]

theorem width_14910 : mW 14910 = 404735922501280 := by
  have hu : mW 14910 ≤ 404735922501280 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14910 ≤ 404735922501279 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14910 : RowArithmetic 14910 (549023055558509201299/500000000000000000000000) (299799923144522556565143/500000000000000000000000) (310482474446871/50000000000000000000000) where
  r0 := (68658379341/125000000000000000)
  k0 := (28029833507799/8000000000000000)
  k6 := (700877037525401/62500000000000000)
  q := (172684683744679568499/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14910]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14910]

theorem width_14911 : mW 14911 = 404830938899219 := by
  have hu : mW 14911 ≤ 404830938899219 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14911 ≤ 404830938899218 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14911 : RowArithmetic 14911 (274505161703380187327/250000000000000000000000) (299794905616718154526179/500000000000000000000000) (1552141869288309/250000000000000000000000) where
  r0 := (549211781107/1000000000000000000)
  k0 := (3503552954893283/1000000000000000000)
  k6 := (560682828094523/50000000000000000)
  q := (34538094909823848013/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14911]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14911]

theorem width_14912 : mW 14912 = 404925971229082 := by
  have hu : mW 14912 ≤ 404925971229082 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14912 ≤ 404925971229081 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14912 : RowArithmetic 14912 (27449879705457978183/25000000000000000000000) (149894944376584517819491/250000000000000000000000) (77593571611523/12500000000000000000000) where
  r0 := (2196626147/4000000000000000)
  k0 := (350337674199657/100000000000000000)
  k6 := (5606640280600451/500000000000000000)
  q := (86348132579691611997/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14912]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14912]

theorem width_14913 : mW 14913 = 405021019492471 := by
  have hu : mW 14913 ≤ 405021019492471 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14913 ≤ 405021019492470 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14913 : RowArithmetic 14913 (1097969735329738533793/1000000000000000000000000) (299784872553734659918107/500000000000000000000000) (6206404244160823/1000000000000000000000000) where
  r0 := (549101301653/1000000000000000000)
  k0 := (3503200549775099/1000000000000000000)
  k6 := (11212904598331399/1000000000000000000)
  q := (43175513893872763029/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14913]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14913]

theorem width_14914 : mW 14914 = 405116083690989 := by
  have hu : mW 14914 ≤ 405116083690989 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14914 ≤ 405116083690988 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14914 : RowArithmetic 14914 (219588857629220837909/200000000000000000000000) (37472482127284310403117/62500000000000000000000) (387832688924237/62500000000000000000000) where
  r0 := (109809215163/200000000000000000)
  k0 := (1751512189114399/500000000000000000)
  k6 := (11212528673275613/1000000000000000000)
  q := (86353922898731126493/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14914]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14914]

theorem width_14915 : mW 14915 = 405211163826238 := by
  have hu : mW 14915 ≤ 405211163826238 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14915 ≤ 405211163826237 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14915 : RowArithmetic 14915 (17154981979152224207/15625000000000000000000) (599549684293296113691631/1000000000000000000000000) (6204242064720401/1000000000000000000000000) where
  r0 := (274495429617/500000000000000000)
  k0 := (1751424113677203/500000000000000000)
  k6 := (11212152786027203/1000000000000000000)
  q := (10794602239082271993/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14915]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14915]

theorem width_14916 : mW 14916 = 405306259899822 := by
  have hu : mW 14916 ≤ 405306259899822 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14916 ≤ 405306259899821 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14916 : RowArithmetic 14916 (6861833818043619289/6250000000000000000000) (599539655877429891158609/1000000000000000000000000) (6203161369876307/1000000000000000000000000) where
  r0 := (548935651907/1000000000000000000)
  k0 := (3502672097145471/1000000000000000000)
  k6 := (2242355387315967/200000000000000000)
  q := (17271942565907287083/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14916]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14916]

theorem width_14917 : mW 14917 = 405401371913344 := by
  have hu : mW 14917 ≤ 405401371913344 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14917 ≤ 405401371913343 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14917 : RowArithmetic 14917 (1097867980808141507419/1000000000000000000000000) (74941203598583691517419/125000000000000000000000) (3101040469086607/500000000000000000000000) where
  r0 := (548880453833/1000000000000000000)
  k0 := (3502495987601921/1000000000000000000)
  k6 := (11211401124927171/1000000000000000000)
  q := (172725215298751328551/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14917]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14917]

theorem width_14918 : mW 14918 = 405496499868406 := by
  have hu : mW 14918 ≤ 405496499868406 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14918 ≤ 405496499868405 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14918 : RowArithmetic 14918 (219568511285511550431/200000000000000000000000) (749399503783417926373/1250000000000000000000) (6201000769528873/1000000000000000000000000) where
  r0 := (34301579063/62500000000000000)
  k0 := (3502319898714109/1000000000000000000)
  k6 := (70068908444143/6250000000000000)
  q := (43182751186092810129/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14918]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14918]

theorem width_14919 : mW 14919 = 405591643766612 := by
  have hu : mW 14919 ≤ 405591643766612 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14919 ≤ 405591643766611 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14919 : RowArithmetic 14919 (68613571108972236157/62500000000000000000000) (299754789295671841042491/500000000000000000000000) (6199920863861037/1000000000000000000000000) where
  r0 := (68596260679/125000000000000000)
  k0 := (3502143830485151/1000000000000000000)
  k6 := (11210649614980627/1000000000000000000)
  q := (86368396997976059461/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14919]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14919]

theorem width_14920 : mW 14920 = 405686803609564 := by
  have hu : mW 14920 ≤ 405686803609564 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14920 ≤ 405686803609563 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14920 : RowArithmetic 14920 (1097791724754464980799/1000000000000000000000000) (14987488887055425975497/25000000000000000000000) (6198841221087523/1000000000000000000000000) where
  r0 := (548714915101/1000000000000000000)
  k0 := (3501967782905399/1000000000000000000)
  k6 := (11210273916674083/1000000000000000000)
  q := (34548516610702694539/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14920]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14920]

theorem width_14921 : mW 14921 = 405781979398866 := by
  have hu : mW 14921 ≤ 405781979398866 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14921 ≤ 405781979398865 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14921 : RowArithmetic 14921 (1097766317458614572043/1000000000000000000000000) (299744766849536987982133/500000000000000000000000) (6197761841126147/1000000000000000000000000) where
  r0 := (274329877007/500000000000000000)
  k0 := (437723969496847/125000000000000000)
  k6 := (11209898256136917/1000000000000000000)
  q := (172748371917074807493/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14921]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14921]

theorem width_14922 : mW 14922 = 405877171136122 := by
  have hu : mW 14922 ≤ 405877171136122 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14922 ≤ 405877171136121 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14922 : RowArithmetic 14922 (548870457927167196383/500000000000000000000000) (29973975662081705147009/50000000000000000000000) (154917068097369/25000000000000000000000) where
  r0 := (68575575271/125000000000000000)
  k0 := (1750807874843411/500000000000000000)
  k6 := (11209522633362803/1000000000000000000)
  q := (34550832117331125141/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14922]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14922]

theorem width_14923 : mW 14923 = 405972378822933 := by
  have hu : mW 14923 ≤ 405972378822933 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14923 ≤ 405972378822932 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14923 : RowArithmetic 14923 (43908620797598244859/40000000000000000000000) (599469494109617160424397/1000000000000000000000000) (774450483663911/125000000000000000000000) where
  r0 := (548549459561/1000000000000000000)
  k0 := (3501439764038267/1000000000000000000)
  k6 := (11209147048345413/1000000000000000000)
  q := (86379974531137713227/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14923]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14923]

theorem width_14924 : mW 14924 = 406067602460905 := by
  have hu : mW 14924 ≤ 406067602460905 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14924 ≤ 406067602460904 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14924 : RowArithmetic 14924 (1097690129713810044479/1000000000000000000000000) (599459476302742894978409/1000000000000000000000000) (6194525277293617/1000000000000000000000000) where
  r0 := (34280895387/62500000000000000)
  k0 := (3501263799029031/1000000000000000000)
  k6 := (11208771501078423/1000000000000000000)
  q := (34553147468790741119/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14924]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14924]

theorem width_14925 : mW 14925 = 406162842051639 := by
  have hu : mW 14925 ≤ 406162842051639 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14925 ≤ 406162842051638 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14925 : RowArithmetic 14925 (54883237258711454617/50000000000000000000000) (149862364955182809488739/250000000000000000000000) (774180868469967/125000000000000000000000) where
  r0 := (548439202057/1000000000000000000)
  k0 := (3501087854649459/1000000000000000000)
  k6 := (11208395991555509/1000000000000000000)
  q := (172771525431709955717/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14925]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14925]

theorem width_14926 : mW 14926 = 406258097596740 := by
  have hu : mW 14926 ≤ 406258097596740 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14926 ≤ 406258097596739 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14926 : RowArithmetic 14926 (274409841579886301879/250000000000000000000000) (599439444663302094739733/1000000000000000000000000) (619236888062761/100000000000000000000000) where
  r0 := (137096021789/250000000000000000)
  k0 := (1750455965451331/500000000000000000)
  k6 := (11208020519770349/1000000000000000000)
  q := (86388656662781833073/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14926]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14926]

theorem width_14927 : mW 14927 = 406353369097810 := by
  have hu : mW 14927 ≤ 406353369097810 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14927 ≤ 406353369097809 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14927 : RowArithmetic 14927 (1097613993148092167973/1000000000000000000000000) (299714715415087753206891/500000000000000000000000) (3095645537907639/500000000000000000000000) where
  r0 := (109665796297/200000000000000000)
  k0 := (175036801388949/50000000000000000)
  k6 := (11207645085716623/1000000000000000000)
  q := (172783101025534322941/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14927]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14927]

theorem width_14928 : mW 14928 = 406448656556455 := by
  have hu : mW 14928 ≤ 406448656556455 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14928 ≤ 406448656556454 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14928 : RowArithmetic 14928 (274397156414550691213/250000000000000000000000) (599419418321071637160069/1000000000000000000000000) (3095106766620377/500000000000000000000000) where
  r0 := (274136942521/500000000000000000)
  k0 := (3500560145275139/1000000000000000000)
  k6 := (11207269689388011/1000000000000000000)
  q := (172788888531641408901/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14928]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14928]

theorem width_14929 : mW 14929 = 406543959974276 := by
  have hu : mW 14929 ≤ 406543959974276 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14929 ≤ 406543959974275 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14929 : RowArithmetic 14929 (1097563263848212429187/1000000000000000000000000) (599409407135710663130411/1000000000000000000000000) (6189136252822157/1000000000000000000000000) where
  r0 := (21928751913/40000000000000000)
  k0 := (1750192141693931/500000000000000000)
  k6 := (11206894330778197/1000000000000000000)
  q := (172794675843904403559/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14929]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14929]

theorem width_14930 : mW 14930 = 406639279352878 := by
  have hu : mW 14930 ≤ 406639279352878 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14930 ≤ 406639279352877 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14930 : RowArithmetic 14930 (1097537907716455605209/1000000000000000000000000) (599399397273812837498889/1000000000000000000000000) (3094029617238789/500000000000000000000000) where
  r0 := (548163719833/1000000000000000000)
  k0 := (1750104221058531/500000000000000000)
  k6 := (350203719058777/31250000000000000)
  q := (172800462962342783187/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14930]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14930]

theorem width_14931 : mW 14931 = 406734614693864 := by
  have hu : mW 14931 ≤ 406734614693864 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14931 ≤ 406734614693863 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14931 : RowArithmetic 14931 (1097512557261268167223/1000000000000000000000000) (299694694367549266657699/500000000000000000000000) (1546745619531293/250000000000000000000000) where
  r0 := (274054325531/500000000000000000)
  k0 := (1750016310726539/500000000000000000)
  k6 := (11206143726689697/1000000000000000000)
  q := (43201562471744005199/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14931]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14931]

theorem width_14932 : mW 14932 = 406829965998838 := by
  have hu : mW 14932 ≤ 406829965998838 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14932 ≤ 406829965998837 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14932 : RowArithmetic 14932 (1097487212480986211183/1000000000000000000000000) (299689690759644109862027/500000000000000000000000) (1546476495920777/250000000000000000000000) where
  r0 := (68506698939/125000000000000000)
  k0 := (3499856821399013/1000000000000000000)
  k6 := (700360530074899/62500000000000000)
  q := (172812036617823586137/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14932]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14932]

theorem width_14933 : mW 14933 = 406925333269405 := by
  have hu : mW 14933 ≤ 406925333269405 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14933 ≤ 406925333269404 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14933 : RowArithmetic 14933 (43898474934957842207/40000000000000000000000) (599369375626102447310909/1000000000000000000000000) (247393190042783/40000000000000000000000) where
  r0 := (273999270589/500000000000000000)
  k0 := (3499681041942009/1000000000000000000)
  k6 := (11205393273400613/1000000000000000000)
  q := (86408911577452472851/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14933]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14933]

theorem width_14934 : mW 14934 = 407020716507167 := by
  have hu : mW 14934 ≤ 407020716507167 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14934 ≤ 407020716507166 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14934 : RowArithmetic 14934 (1097436539938485847379/1000000000000000000000000) (599359371055261731561321/1000000000000000000000000) (1545938445050709/250000000000000000000000) where
  r0 := (547943500061/1000000000000000000)
  k0 := (1749752641544181/500000000000000000)
  k6 := (11205018103290073/1000000000000000000)
  q := (172823609498239562721/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14934]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14934]

theorem width_14935 : mW 14935 = 407116115713729 := by
  have hu : mW 14935 ≤ 407116115713729 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14935 ≤ 407116115713728 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14935 : RowArithmetic 14935 (548705606086471576567/500000000000000000000000) (599349367806486859586151/1000000000000000000000000) (1236535614200229/200000000000000000000000) where
  r0 := (136972117039/250000000000000000)
  k0 := (3499329544825209/1000000000000000000)
  k6 := (11204642970860457/1000000000000000000)
  q := (10801837227990431073/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14935]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14935]

theorem width_14936 : mW 14936 = 407211530890694 := by
  have hu : mW 14936 ≤ 407211530890694 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14936 ≤ 407211530890693 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14936 : RowArithmetic 14936 (274346472518914241193/250000000000000000000000) (149834841469874625917781/250000000000000000000000) (6181602623382813/1000000000000000000000000) where
  r0 := (547833445463/1000000000000000000)
  k0 := (3499153827155653/1000000000000000000)
  k6 := (700266742256591/62500000000000000)
  q := (172835181603746405761/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14936]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14936]

theorem width_14937 : mW 14937 = 407306962039667 := by
  have hu : mW 14937 ≤ 407306962039667 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14937 ≤ 407306962039666 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14937 : RowArithmetic 14937 (274340143411241523537/250000000000000000000000) (299664682637008780322297/500000000000000000000000) (3090263718633079/500000000000000000000000) where
  r0 := (547778431979/1000000000000000000)
  k0 := (699795626014643/200000000000000000)
  k6 := (5601946409509383/500000000000000000)
  q := (172840967365957541959/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14937]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14937]

theorem width_14938 : mW 14938 = 407402409162252 := by
  have hu : mW 14938 ≤ 407402409162252 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14938 ≤ 407402409162251 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14938 : RowArithmetic 14938 (274333815719802594409/250000000000000000000000) (5993193659897649835959/10000000000000000000000) (308972625628477/50000000000000000000000) where
  r0 := (273861713851/500000000000000000)
  k0 := (3498802453574609/1000000000000000000)
  k6 := (11203517799594081/1000000000000000000)
  q := (86423376467249877983/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14938]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14938]

theorem width_14939 : mW 14939 = 407497872260053 := by
  have hu : mW 14939 ≤ 407497872260053 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14939 ≤ 407497872260052 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14939 : RowArithmetic 14939 (1097309957776730273953/1000000000000000000000000) (299654684013230859931107/500000000000000000000000) (1235675569842271/200000000000000000000000) where
  r0 := (547668432629/1000000000000000000)
  k0 := (3498626797653353/1000000000000000000)
  k6 := (112031428178251/10000000000000000)
  q := (17285253830939249473/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14939]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14939]

theorem width_14940 : mW 14940 = 407593351334674 := by
  have hu : mW 14940 ≤ 407593351334674 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14940 ≤ 407593351334673 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14940 : RowArithmetic 14940 (1097284658335866863863/1000000000000000000000000) (149824842845957227906061/250000000000000000000000) (6177303447110029/1000000000000000000000000) where
  r0 := (273806723379/500000000000000000)
  k0 := (3498451162306157/1000000000000000000)
  k6 := (11202767873705521/1000000000000000000)
  q := (172858323490655201947/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14940]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14940]

theorem width_14941 : mW 14941 = 407688846387719 := by
  have hu : mW 14941 ≤ 407688846387719 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14941 ≤ 407688846387718 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14941 : RowArithmetic 14941 (548629682277480924937/500000000000000000000000) (11985787521231754561827/20000000000000000000000) (308811465309201/50000000000000000000000) where
  r0 := (68444808761/125000000000000000)
  k0 := (3498275547532927/1000000000000000000)
  k6 := (2800598241807261/250000000000000000)
  q := (21608013559788414757/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14941]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14941]

theorem width_14942 : mW 14942 = 407784357420793 := by
  have hu : mW 14942 ≤ 407784357420793 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14942 ≤ 407784357420792 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14942 : RowArithmetic 14942 (219446815286471431063/200000000000000000000000) (74909922757432425588193/125000000000000000000000) (3087577713175901/500000000000000000000000) where
  r0 := (547503502617/1000000000000000000)
  k0 := (874524988332593/250000000000000000)
  k6 := (2800504524597343/250000000000000000)
  q := (21608736659046035031/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14942]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14942]

theorem width_14943 : mW 14943 = 407879884435500 := by
  have hu : mW 14943 ≤ 407879884435500 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14943 ≤ 407879884435499 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14943 : RowArithmetic 14943 (548604396983197862873/500000000000000000000000) (599269389377165259933969/1000000000000000000000000) (6174081807531899/1000000000000000000000000) where
  r0 := (547448544341/1000000000000000000)
  k0 := (3497924379688811/1000000000000000000)
  k6 := (5600821633590103/500000000000000000)
  q := (21609459734107190307/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14943]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14943]

theorem width_14944 : mW 14944 = 407975427433444 := by
  have hu : mW 14944 ≤ 407975427433444 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14944 ≤ 407975427433443 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14944 : RowArithmetic 14944 (219436703431084225513/200000000000000000000000) (599259398014426744910811/1000000000000000000000000) (3086504224821431/500000000000000000000000) where
  r0 := (547393595259/1000000000000000000)
  k0 := (699549765321629/200000000000000000)
  k6 := (2800317118398813/250000000000000000)
  q := (172881462279794475367/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14944]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14944]

theorem width_14945 : mW 14945 = 408070986416230 := by
  have hu : mW 14945 ≤ 408070986416230 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14945 ≤ 408070986416229 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14945 : RowArithmetic 14945 (27428956149944428689/25000000000000000000000) (74906175996370666476563/125000000000000000000000) (48218244942213/7812500000000000000000) where
  r0 := (547338655369/1000000000000000000)
  k0 := (3497573294085079/1000000000000000000)
  k6 := (2240178743525643/200000000000000000)
  q := (86443623246599283207/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14945]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14945]

theorem width_14946 : mW 14946 = 408166561385462 := by
  have hu : mW 14946 ≤ 408166561385462 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14946 ≤ 408166561385461 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14946 : RowArithmetic 14946 (548566490245904296689/500000000000000000000000) (5992394192465026078477/10000000000000000000000) (3085431258165861/500000000000000000000000) where
  r0 := (547283724669/1000000000000000000)
  k0 := (21858736138227/6250000000000000)
  k6 := (2240103799854561/200000000000000000)
  q := (86446515256544609891/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14946]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14946]

theorem width_14947 : mW 14947 = 408262152342745 := by
  have hu : mW 14947 ≤ 408262152342745 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14947 ≤ 408262152342744 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14947 : RowArithmetic 14947 (1097107720635860492763/1000000000000000000000000) (74903678980095024480531/125000000000000000000000) (6169789940746869/1000000000000000000000000) where
  r0 := (109445760631/200000000000000000)
  k0 := (3497222290692179/1000000000000000000)
  k6 := (1400018039815341/125000000000000000)
  q := (172898814339485856407/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14947]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14947]

theorem width_14948 : mW 14948 = 408357759289683 := by
  have hu : mW 14948 ≤ 408357759289683 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14948 ≤ 408357759289682 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14948 : RowArithmetic 14948 (548541233214139446703/500000000000000000000000) (299609722876729961102099/500000000000000000000000) (3084358812883693/500000000000000000000000) where
  r0 := (136793472707/250000000000000000)
  k0 := (1748523409909473/500000000000000000)
  k6 := (11199769675371697/1000000000000000000)
  q := (6916183918896315759/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14948]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14948]

theorem width_14949 : mW 14949 = 408453382227881 := by
  have hu : mW 14949 ≤ 408453382227881 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14949 ≤ 408453382227880 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14949 : RowArithmetic 14949 (137132152233426257851/125000000000000000000000) (599209460984323498445679/1000000000000000000000000) (1541911392827993/250000000000000000000000) where
  r0 := (547118987683/1000000000000000000)
  k0 := (699374273896747/200000000000000000)
  k6 := (11199395069813423/1000000000000000000)
  q := (86455190705937373463/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14949]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14949]

theorem width_14950 : mW 14950 = 408549021158945 := by
  have hu : mW 14950 ≤ 408549021158945 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14950 ≤ 408549021158944 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14950 : RowArithmetic 14950 (1097031974951600488761/1000000000000000000000000) (299599738766536430915877/500000000000000000000000) (308328688864967/50000000000000000000000) where
  r0 := (547064093719/1000000000000000000)
  k0 := (3496695939686443/1000000000000000000)
  k6 := (11199020501841619/1000000000000000000)
  q := (86458082328952913227/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14950]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14950]

theorem width_14951 : mW 14951 = 408644676084477 := by
  have hu : mW 14951 ≤ 408644676084477 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14951 ≤ 408644676084476 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14951 : RowArithmetic 14951 (1097006737679198875903/1000000000000000000000000) (149797373849857496278689/250000000000000000000000) (3082751121824149/500000000000000000000000) where
  r0 := (273504604467/500000000000000000)
  k0 := (3496520530423767/1000000000000000000)
  k6 := (11198645971450001/1000000000000000000)
  q := (34584389542104108101/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14951]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14951]

theorem width_14952 : mW 14952 = 408740347006085 := by
  have hu : mW 14952 ≤ 408740347006085 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14952 ≤ 408740347006084 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14952 : RowArithmetic 14952 (219396301209710430341/200000000000000000000000) (119835902916623400079501/200000000000000000000000) (6164430970277593/1000000000000000000000000) where
  r0 := (273477166663/500000000000000000)
  k0 := (437043142711551/125000000000000000)
  k6 := (2799567869658071/250000000000000000)
  q := (86463865284869146891/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14952]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14952]

theorem width_14953 : mW 14953 = 408836033925371 := by
  have hu : mW 14953 ≤ 408836033925371 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14953 ≤ 408836033925370 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14953 : RowArithmetic 14953 (34279883751812820553/31250000000000000000000) (299584767541927972739397/500000000000000000000000) (3081679978553047/500000000000000000000000) where
  r0 := (136724866723/250000000000000000)
  k0 := (699233954697173/200000000000000000)
  k6 := (2799474255845547/250000000000000000)
  q := (172933513235578487741/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14953]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14953]

theorem width_14954 : mW 14954 = 408931736843942 := by
  have hu : mW 14954 ≤ 408931736843942 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14954 ≤ 408931736843941 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14954 : RowArithmetic 14954 (1096931059705921758253/1000000000000000000000000) (599159556901369064633029/1000000000000000000000000) (1540572301013157/250000000000000000000000) where
  r0 := (546844609631/1000000000000000000)
  k0 := (3495994425804031/1000000000000000000)
  k6 := (1119752260569343/100000000000000000)
  q := (172939295708060520597/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14954]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14954]

theorem width_14955 : mW 14955 = 409027455763401 := by
  have hu : mW 14955 ≤ 409027455763401 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14955 ≤ 409027455763400 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14955 : RowArithmetic 14955 (548452922495318715769/500000000000000000000000) (599149580035378721686097/1000000000000000000000000) (3080609355518057/500000000000000000000000) where
  r0 := (27339488077/50000000000000000)
  k0 := (873954774660101/250000000000000000)
  k6 := (11197148225559733/1000000000000000000)
  q := (4323626949680094683/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14955]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14955]

theorem width_14956 : mW 14956 = 409123190685356 := by
  have hu : mW 14956 ≤ 409123190685356 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14956 ≤ 409123190685355 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14956 : RowArithmetic 14956 (548440317955253340067/500000000000000000000000) (149784901121401801326839/250000000000000000000000) (246405939119017/40000000000000000000000) where
  r0 := (546734922617/1000000000000000000)
  k0 := (3495643791991677/1000000000000000000)
  k6 := (5598386941487409/500000000000000000)
  q := (172950860073027679639/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14956]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14956]

theorem width_14957 : mW 14957 = 409218941611409 := by
  have hu : mW 14957 ≤ 409218941611409 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14957 ≤ 409218941611408 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14957 : RowArithmetic 14957 (1096855432463881915763/1000000000000000000000000) (599129630251777032716557/1000000000000000000000000) (6159078504789559/1000000000000000000000000) where
  r0 := (27334004643/50000000000000000)
  k0 := (699093701170909/200000000000000000)
  k6 := (11196399577932409/1000000000000000000)
  q := (172956641965551586041/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14957]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14957]

theorem width_14958 : mW 14958 = 409314708543167 := by
  have hu : mW 14958 ≤ 409314708543167 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14958 ≤ 409314708543166 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14958 : RowArithmetic 14958 (1096830234649114174899/1000000000000000000000000) (149779914333402689156381/250000000000000000000000) (1539502197849367/250000000000000000000000) where
  r0 := (546625272267/1000000000000000000)
  k0 := (3495293240225697/1000000000000000000)
  k6 := (11196025310426231/1000000000000000000)
  q := (172962423664794891773/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14958]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14958]

theorem width_14959 : mW 14959 = 409410491482234 := by
  have hu : mW 14959 ≤ 409410491482234 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14959 ≤ 409410491482233 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14959 : RowArithmetic 14959 (137100630308069538269/125000000000000000000000) (119821937146166194464637/200000000000000000000000) (6156939337718183/1000000000000000000000000) where
  r0 := (109314092167/200000000000000000)
  k0 := (873779498774657/250000000000000000)
  k6 := (11195651080450011/1000000000000000000)
  q := (172968205170776978841/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14959]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14959]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 14885 then ⟨(68667786175842178633/62500000000000000000000), (599851155269097255950119/1000000000000000000000000), (3118392839964409/500000000000000000000000)⟩ else
  if n = 14886 then ⟨(68666185703519715631/62500000000000000000000), (599841086909126628019371/1000000000000000000000000), (6235697052445529/1000000000000000000000000)⟩ else
  if n = 14887 then ⟨(219726673889906723473/200000000000000000000000), (599831019884720777949019/1000000000000000000000000), (6234608690585853/1000000000000000000000000)⟩ else
  if n = 14888 then ⟨(1098607773391437720911/1000000000000000000000000), (599820954195596525072899/1000000000000000000000000), (6233520594266539/1000000000000000000000000)⟩ else
  if n = 14889 then ⟨(549291091540169197653/500000000000000000000000), (299905444920735403018481/500000000000000000000000), (1558108190851107/250000000000000000000000)⟩ else
  if n = 14890 then ⟨(274639149628636523057/250000000000000000000000), (599800826822060595067291/1000000000000000000000000), (1557836299479091/250000000000000000000000)⟩ else
  if n = 14891 then ⟨(274632754923092974773/250000000000000000000000), (299895382568541535435653/500000000000000000000000), (778782237214903/125000000000000000000000)⟩ else
  if n = 14892 then ⟨(1098505446612127947249/1000000000000000000000000), (74972588098281914608077/125000000000000000000000), (622917086272993/100000000000000000000000)⟩ else
  if n = 14893 then ⟨(1098479879272127002533/1000000000000000000000000), (599770645769294647532037/1000000000000000000000000), (6228084092865441/1000000000000000000000000)⟩ else
  if n = 14894 then ⟨(549227158835340824281/500000000000000000000000), (119952117617183677665471/200000000000000000000000), (1245399517608543/200000000000000000000000)⟩ else
  if n = 14895 then ⟨(549214380903052960081/500000000000000000000000), (299875265867921958456231/500000000000000000000000), (3112955674089387/500000000000000000000000)⟩ else
  if n = 14896 then ⟨(1098403211676714077837/1000000000000000000000000), (599740476718788827390593/1000000000000000000000000), (6224825373190657/1000000000000000000000000)⟩ else
  if n = 14897 then ⟨(1098377667280821015981/1000000000000000000000000), (599730423034470628652913/1000000000000000000000000), (1555934915748859/250000000000000000000000)⟩ else
  if n = 14898 then ⟨(1098352128616742262561/1000000000000000000000000), (599720370682607045912821/1000000000000000000000000), (1244530843502043/200000000000000000000000)⟩ else
  if n = 14899 then ⟨(1098326595682794386209/1000000000000000000000000), (599710319662915768012707/1000000000000000000000000), (3110784518326073/500000000000000000000000)⟩ else
  if n = 14900 then ⟨(274575267119323443353/250000000000000000000000), (599700269975114694058213/1000000000000000000000000), (6220484120338383/1000000000000000000000000)⟩ else
  if n = 14901 then ⟨(219655109399711488789/200000000000000000000000), (599690221618921708964709/1000000000000000000000000), (6219399468486113/1000000000000000000000000)⟩ else
  if n = 14902 then ⟨(549125015622452135661/500000000000000000000000), (599680174594054801559783/1000000000000000000000000), (6218315081012599/1000000000000000000000000)⟩ else
  if n = 14903 then ⟨(549112260607326269773/500000000000000000000000), (149917532225058003997619/250000000000000000000000), (3108615478917547/500000000000000000000000)⟩ else
  if n = 14904 then ⟨(1098199016906121164989/1000000000000000000000000), (59966008453717158135189/100000000000000000000000), (38850919367943/6250000000000000000000)⟩ else
  if n = 14905 then ⟨(549086759158815051263/500000000000000000000000), (119930008300918342500729/200000000000000000000000), (621506350403729/100000000000000000000000)⟩ else
  if n = 14906 then ⟨(549074012723750172217/500000000000000000000000), (11992799996044214684991/20000000000000000000000), (6213980173251703/1000000000000000000000000)⟩ else
  if n = 14907 then ⟨(1098122538294051888671/1000000000000000000000000), (149907489857436768770347/250000000000000000000000), (1553224276607867/250000000000000000000000)⟩ else
  if n = 14908 then ⟨(549048528427803697717/500000000000000000000000), (149904980096729798412937/250000000000000000000000), (1242362860698809/200000000000000000000000)⟩ else
  if n = 14909 then ⟨(1098071581130488530623/1000000000000000000000000), (149902470668361413823661/250000000000000000000000), (1242146352871373/200000000000000000000000)⟩ else
  if n = 14910 then ⟨(549023055558509201299/500000000000000000000000), (299799923144522556565143/500000000000000000000000), (310482474446871/50000000000000000000000)⟩ else
  if n = 14911 then ⟨(274505161703380187327/250000000000000000000000), (299794905616718154526179/500000000000000000000000), (1552141869288309/250000000000000000000000)⟩ else
  if n = 14912 then ⟨(27449879705457978183/25000000000000000000000), (149894944376584517819491/250000000000000000000000), (77593571611523/12500000000000000000000)⟩ else
  if n = 14913 then ⟨(1097969735329738533793/1000000000000000000000000), (299784872553734659918107/500000000000000000000000), (6206404244160823/1000000000000000000000000)⟩ else
  if n = 14914 then ⟨(219588857629220837909/200000000000000000000000), (37472482127284310403117/62500000000000000000000), (387832688924237/62500000000000000000000)⟩ else
  if n = 14915 then ⟨(17154981979152224207/15625000000000000000000), (599549684293296113691631/1000000000000000000000000), (6204242064720401/1000000000000000000000000)⟩ else
  if n = 14916 then ⟨(6861833818043619289/6250000000000000000000), (599539655877429891158609/1000000000000000000000000), (6203161369876307/1000000000000000000000000)⟩ else
  if n = 14917 then ⟨(1097867980808141507419/1000000000000000000000000), (74941203598583691517419/125000000000000000000000), (3101040469086607/500000000000000000000000)⟩ else
  if n = 14918 then ⟨(219568511285511550431/200000000000000000000000), (749399503783417926373/1250000000000000000000), (6201000769528873/1000000000000000000000000)⟩ else
  if n = 14919 then ⟨(68613571108972236157/62500000000000000000000), (299754789295671841042491/500000000000000000000000), (6199920863861037/1000000000000000000000000)⟩ else
  if n = 14920 then ⟨(1097791724754464980799/1000000000000000000000000), (14987488887055425975497/25000000000000000000000), (6198841221087523/1000000000000000000000000)⟩ else
  if n = 14921 then ⟨(1097766317458614572043/1000000000000000000000000), (299744766849536987982133/500000000000000000000000), (6197761841126147/1000000000000000000000000)⟩ else
  if n = 14922 then ⟨(548870457927167196383/500000000000000000000000), (29973975662081705147009/50000000000000000000000), (154917068097369/25000000000000000000000)⟩ else
  if n = 14923 then ⟨(43908620797598244859/40000000000000000000000), (599469494109617160424397/1000000000000000000000000), (774450483663911/125000000000000000000000)⟩ else
  if n = 14924 then ⟨(1097690129713810044479/1000000000000000000000000), (599459476302742894978409/1000000000000000000000000), (6194525277293617/1000000000000000000000000)⟩ else
  if n = 14925 then ⟨(54883237258711454617/50000000000000000000000), (149862364955182809488739/250000000000000000000000), (774180868469967/125000000000000000000000)⟩ else
  if n = 14926 then ⟨(274409841579886301879/250000000000000000000000), (599439444663302094739733/1000000000000000000000000), (619236888062761/100000000000000000000000)⟩ else
  if n = 14927 then ⟨(1097613993148092167973/1000000000000000000000000), (299714715415087753206891/500000000000000000000000), (3095645537907639/500000000000000000000000)⟩ else
  if n = 14928 then ⟨(274397156414550691213/250000000000000000000000), (599419418321071637160069/1000000000000000000000000), (3095106766620377/500000000000000000000000)⟩ else
  if n = 14929 then ⟨(1097563263848212429187/1000000000000000000000000), (599409407135710663130411/1000000000000000000000000), (6189136252822157/1000000000000000000000000)⟩ else
  if n = 14930 then ⟨(1097537907716455605209/1000000000000000000000000), (599399397273812837498889/1000000000000000000000000), (3094029617238789/500000000000000000000000)⟩ else
  if n = 14931 then ⟨(1097512557261268167223/1000000000000000000000000), (299694694367549266657699/500000000000000000000000), (1546745619531293/250000000000000000000000)⟩ else
  if n = 14932 then ⟨(1097487212480986211183/1000000000000000000000000), (299689690759644109862027/500000000000000000000000), (1546476495920777/250000000000000000000000)⟩ else
  if n = 14933 then ⟨(43898474934957842207/40000000000000000000000), (599369375626102447310909/1000000000000000000000000), (247393190042783/40000000000000000000000)⟩ else
  if n = 14934 then ⟨(1097436539938485847379/1000000000000000000000000), (599359371055261731561321/1000000000000000000000000), (1545938445050709/250000000000000000000000)⟩ else
  if n = 14935 then ⟨(548705606086471576567/500000000000000000000000), (599349367806486859586151/1000000000000000000000000), (1236535614200229/200000000000000000000000)⟩ else
  if n = 14936 then ⟨(274346472518914241193/250000000000000000000000), (149834841469874625917781/250000000000000000000000), (6181602623382813/1000000000000000000000000)⟩ else
  if n = 14937 then ⟨(274340143411241523537/250000000000000000000000), (299664682637008780322297/500000000000000000000000), (3090263718633079/500000000000000000000000)⟩ else
  if n = 14938 then ⟨(274333815719802594409/250000000000000000000000), (5993193659897649835959/10000000000000000000000), (308972625628477/50000000000000000000000)⟩ else
  if n = 14939 then ⟨(1097309957776730273953/1000000000000000000000000), (299654684013230859931107/500000000000000000000000), (1235675569842271/200000000000000000000000)⟩ else
  if n = 14940 then ⟨(1097284658335866863863/1000000000000000000000000), (149824842845957227906061/250000000000000000000000), (6177303447110029/1000000000000000000000000)⟩ else
  if n = 14941 then ⟨(548629682277480924937/500000000000000000000000), (11985787521231754561827/20000000000000000000000), (308811465309201/50000000000000000000000)⟩ else
  if n = 14942 then ⟨(219446815286471431063/200000000000000000000000), (74909922757432425588193/125000000000000000000000), (3087577713175901/500000000000000000000000)⟩ else
  if n = 14943 then ⟨(548604396983197862873/500000000000000000000000), (599269389377165259933969/1000000000000000000000000), (6174081807531899/1000000000000000000000000)⟩ else
  if n = 14944 then ⟨(219436703431084225513/200000000000000000000000), (599259398014426744910811/1000000000000000000000000), (3086504224821431/500000000000000000000000)⟩ else
  if n = 14945 then ⟨(27428956149944428689/25000000000000000000000), (74906175996370666476563/125000000000000000000000), (48218244942213/7812500000000000000000)⟩ else
  if n = 14946 then ⟨(548566490245904296689/500000000000000000000000), (5992394192465026078477/10000000000000000000000), (3085431258165861/500000000000000000000000)⟩ else
  if n = 14947 then ⟨(1097107720635860492763/1000000000000000000000000), (74903678980095024480531/125000000000000000000000), (6169789940746869/1000000000000000000000000)⟩ else
  if n = 14948 then ⟨(548541233214139446703/500000000000000000000000), (299609722876729961102099/500000000000000000000000), (3084358812883693/500000000000000000000000)⟩ else
  if n = 14949 then ⟨(137132152233426257851/125000000000000000000000), (599209460984323498445679/1000000000000000000000000), (1541911392827993/250000000000000000000000)⟩ else
  if n = 14950 then ⟨(1097031974951600488761/1000000000000000000000000), (299599738766536430915877/500000000000000000000000), (308328688864967/50000000000000000000000)⟩ else
  if n = 14951 then ⟨(1097006737679198875903/1000000000000000000000000), (149797373849857496278689/250000000000000000000000), (3082751121824149/500000000000000000000000)⟩ else
  if n = 14952 then ⟨(219396301209710430341/200000000000000000000000), (119835902916623400079501/200000000000000000000000), (6164430970277593/1000000000000000000000000)⟩ else
  if n = 14953 then ⟨(34279883751812820553/31250000000000000000000), (299584767541927972739397/500000000000000000000000), (3081679978553047/500000000000000000000000)⟩ else
  if n = 14954 then ⟨(1096931059705921758253/1000000000000000000000000), (599159556901369064633029/1000000000000000000000000), (1540572301013157/250000000000000000000000)⟩ else
  if n = 14955 then ⟨(548452922495318715769/500000000000000000000000), (599149580035378721686097/1000000000000000000000000), (3080609355518057/500000000000000000000000)⟩ else
  if n = 14956 then ⟨(548440317955253340067/500000000000000000000000), (149784901121401801326839/250000000000000000000000), (246405939119017/40000000000000000000000)⟩ else
  if n = 14957 then ⟨(1096855432463881915763/1000000000000000000000000), (599129630251777032716557/1000000000000000000000000), (6159078504789559/1000000000000000000000000)⟩ else
  if n = 14958 then ⟨(1096830234649114174899/1000000000000000000000000), (149779914333402689156381/250000000000000000000000), (1539502197849367/250000000000000000000000)⟩ else
  ⟨(137100630308069538269/125000000000000000000000), (119821937146166194464637/200000000000000000000000), (6156939337718183/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14885 ≤ n) (hb : n ≤ 14959) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14885
  · exact row_14886
  · exact row_14887
  · exact row_14888
  · exact row_14889
  · exact row_14890
  · exact row_14891
  · exact row_14892
  · exact row_14893
  · exact row_14894
  · exact row_14895
  · exact row_14896
  · exact row_14897
  · exact row_14898
  · exact row_14899
  · exact row_14900
  · exact row_14901
  · exact row_14902
  · exact row_14903
  · exact row_14904
  · exact row_14905
  · exact row_14906
  · exact row_14907
  · exact row_14908
  · exact row_14909
  · exact row_14910
  · exact row_14911
  · exact row_14912
  · exact row_14913
  · exact row_14914
  · exact row_14915
  · exact row_14916
  · exact row_14917
  · exact row_14918
  · exact row_14919
  · exact row_14920
  · exact row_14921
  · exact row_14922
  · exact row_14923
  · exact row_14924
  · exact row_14925
  · exact row_14926
  · exact row_14927
  · exact row_14928
  · exact row_14929
  · exact row_14930
  · exact row_14931
  · exact row_14932
  · exact row_14933
  · exact row_14934
  · exact row_14935
  · exact row_14936
  · exact row_14937
  · exact row_14938
  · exact row_14939
  · exact row_14940
  · exact row_14941
  · exact row_14942
  · exact row_14943
  · exact row_14944
  · exact row_14945
  · exact row_14946
  · exact row_14947
  · exact row_14948
  · exact row_14949
  · exact row_14950
  · exact row_14951
  · exact row_14952
  · exact row_14953
  · exact row_14954
  · exact row_14955
  · exact row_14956
  · exact row_14957
  · exact row_14958
  · exact row_14959

end BstLean.Part271.R3.Rows14885
