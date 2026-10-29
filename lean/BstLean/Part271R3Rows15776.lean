import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15776–15850. -/
namespace BstLean.Part271.R3.Rows15776
open Real BstLean.Part130 BstLean.Part227

theorem width_15776 : mW 15776 = 493161473573927 := by
  have hu : mW 15776 ≤ 493161473573927 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15776 ≤ 493161473573926 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15776 : RowArithmetic 15776 (538982239762338498237/500000000000000000000000) (18480579365970767474437/31250000000000000000000) (5363128289480121/1000000000000000000000000) where
  r0 := (1261666763/2500000000000000)
  k0 := (839616760091323/250000000000000000)
  k6 := (10901899828850757/1000000000000000000)
  q := (44407206622349035117/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15776]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15776]

theorem width_15777 : mW 15777 = 493270893067168 := by
  have hu : mW 15777 ≤ 493270893067168 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15777 ≤ 493270893067167 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15777 : RowArithmetic 15777 (269485847758497678947/250000000000000000000000) (295684779008924252163167/500000000000000000000000) (536224673516923/100000000000000000000000) where
  r0 := (252309362359/500000000000000000)
  k0 := (3358307385789351/1000000000000000000)
  k6 := (10901554323603111/1000000000000000000)
  q := (44408614029262385887/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15777]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15777]

theorem width_15778 : mW 15778 = 493380329900234 := by
  have hu : mW 15778 ≤ 493380329900234 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15778 ≤ 493380329900233 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15778 : RowArithmetic 15778 (538961153501392472553/500000000000000000000000) (147840144359333181348377/250000000000000000000000) (2680682691722441/500000000000000000000000) where
  r0 := (504570751839/1000000000000000000)
  k0 := (3358147748923751/1000000000000000000)
  k6 := (10901208851202853/1000000000000000000)
  q := (177640085566293285323/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15778]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15778]

theorem width_15779 : mW 15779 = 493489784074772 := by
  have hu : mW 15779 ≤ 493489784074772 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15779 ≤ 493489784074771 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15779 : RowArithmetic 15779 (67368826714364078449/62500000000000000000000) (591351597969296805473891/1000000000000000000000000) (1340121058561829/250000000000000000000000) where
  r0 := (394158427/781250000000000)
  k0 := (3357988129761033/1000000000000000000)
  k6 := (5450431705822389/500000000000000000)
  q := (11102857177321520423/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15779]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15779]

theorem width_15780 : mW 15780 = 493599255592432 := by
  have hu : mW 15780 ≤ 493599255592432 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15780 ≤ 493599255592431 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15780 : RowArithmetic 15780 (1077880152313876778829/1000000000000000000000000) (591342619613520464330997/1000000000000000000000000) (1339900821879189/250000000000000000000000) where
  r0 := (6305935361/12500000000000000)
  k0 := (839457132075099/250000000000000000)
  k6 := (2725129501230921/250000000000000000)
  q := (177651343929619626169/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15780]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15780]

theorem width_15781 : mW 15781 = 493708744454862 := by
  have hu : mW 15781 ≤ 493708744454862 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15781 ≤ 493708744454861 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15781 : RowArithmetic 15781 (53892954082685283501/50000000000000000000000) (295666821184891752709069/500000000000000000000000) (214348901727739/40000000000000000000000) where
  r0 := (504426878797/1000000000000000000)
  k0 := (1678834472268853/500000000000000000)
  k6 := (21289399669989/1953125000000000)
  q := (88828486421868069563/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15781]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15781]

theorem width_15782 : mW 15782 = 493818250663711 := by
  have hu : mW 15782 ≤ 493818250663711 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15782 ≤ 493818250663710 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15782 : RowArithmetic 15782 (107783801544807822833/100000000000000000000000) (295662333118932824733373/500000000000000000000000) (669730250152219/125000000000000000000000) where
  r0 := (50437893631/100000000000000000)
  k0 := (3357509378472159/1000000000000000000)
  k6 := (2724956822492907/250000000000000000)
  q := (35532520315902163711/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15782]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15782]

theorem width_15783 : mW 15783 = 493927774220628 := by
  have hu : mW 15783 ≤ 493927774220628 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15783 ≤ 493927774220627 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15783 : RowArithmetic 15783 (107781695369576119059/100000000000000000000000) (591315691217546856941591/1000000000000000000000000) (1339240415382473/250000000000000000000000) where
  r0 := (504331001417/1000000000000000000)
  k0 := (3357349830099621/1000000000000000000)
  k6 := (5449740990865133/500000000000000000)
  q := (35533646027392122937/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15783]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15783]

theorem width_15784 : mW 15784 = 494037315127262 := by
  have hu : mW 15784 ≤ 494037315127262 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15784 ≤ 494037315127261 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15784 : RowArithmetic 15784 (8420280440590013521/7812500000000000000000) (591306717308607067443937/1000000000000000000000000) (267804076203511/50000000000000000000000) where
  r0 := (126070768529/250000000000000000)
  k0 := (3357190299415957/1000000000000000000)
  k6 := (10899136706305083/1000000000000000000)
  q := (88836929258051237529/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15784]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15784]

theorem width_15785 : mW 15785 = 494146873385261 := by
  have hu : mW 15785 ≤ 494146873385261 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15785 ≤ 494146873385260 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15785 : RowArithmetic 15785 (13472185544326596881/12500000000000000000000) (147824436127706572006543/250000000000000000000000) (1071040317755819/200000000000000000000000) where
  r0 := (100847030881/200000000000000000)
  k0 := (419628848302129/125000000000000000)
  k6 := (5449395731845441/500000000000000000)
  q := (22209935839619168067/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15785]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15785]

theorem width_15786 : mW 15786 = 494256448996275 := by
  have hu : mW 15786 ≤ 494256448996275 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15786 ≤ 494256448996274 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15786 : RowArithmetic 15786 (538876897573173503021/500000000000000000000000) (295644386411992264209271/500000000000000000000000) (1713382993791/320000000000000000000) where
  r0 := (504187242283/1000000000000000000)
  k0 := (839217822775509/250000000000000000)
  k6 := (2179689250776493/200000000000000000)
  q := (88842557369765082647/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15786]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15786]

theorem width_15787 : mW 15787 = 494366041961953 := by
  have hu : mW 15787 ≤ 494366041961953 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15787 ≤ 494366041961952 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15787 : RowArithmetic 15787 (1077732751194947981233/1000000000000000000000000) (147819950561965487784523/250000000000000000000000) (5353442324463953/1000000000000000000000000) where
  r0 := (504139337749/1000000000000000000)
  k0 := (3356711813470163/1000000000000000000)
  k6 := (10898101076874639/1000000000000000000)
  q := (7107629703353995073/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15787]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15787]

theorem width_15788 : mW 15788 = 494475652283943 := by
  have hu : mW 15788 ≤ 494475652283943 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15788 ≤ 494475652283942 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15788 : RowArithmetic 15788 (1077711711690699886957/1000000000000000000000000) (591270832782238758237141/1000000000000000000000000) (334535187207547/62500000000000000000000) where
  r0 := (630114301/1250000000000000)
  k0 := (671310470702789/200000000000000000)
  k6 := (170277436447847/15625000000000000)
  q := (177696370249929415941/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15788]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15788]

theorem width_15789 : mW 15789 = 494585279963895 := by
  have hu : mW 15789 ≤ 494585279963895 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15789 ≤ 494585279963894 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15789 : RowArithmetic 15789 (538845338316185894191/500000000000000000000000) (591261864426895139620933/1000000000000000000000000) (2675841934053849/500000000000000000000000) where
  r0 := (100808710287/200000000000000000)
  k0 := (3356392911232571/1000000000000000000)
  k6 := (544870541061999/50000000000000000)
  q := (177701997737785716769/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15789]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15789]

theorem width_15790 : mW 15790 = 494694925003458 := by
  have hu : mW 15790 ≤ 494694925003458 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15790 ≤ 494694925003457 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15790 : RowArithmetic 15790 (538834823009366738769/500000000000000000000000) (295626448590805716810483/500000000000000000000000) (5350804942765249/1000000000000000000000000) where
  r0 := (503995669651/1000000000000000000)
  k0 := (839058371654643/250000000000000000)
  k6 := (2724266435650691/250000000000000000)
  q := (88853812523717855379/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15790]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15790]

theorem width_15791 : mW 15791 = 494804587404282 := by
  have hu : mW 15791 ≤ 494804587404282 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15791 ≤ 494804587404281 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15791 : RowArithmetic 15791 (269412154962138722911/250000000000000000000000) (59124393104616800476407/100000000000000000000000) (5349926219233873/1000000000000000000000000) where
  r0 := (503947795449/1000000000000000000)
  k0 := (1678037039838897/500000000000000000)
  k6 := (1362090087093171/125000000000000000)
  q := (88856626089448163337/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15791]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15791]

theorem width_15792 : mW 15792 = 494914267168015 := by
  have hu : mW 15792 ≤ 494914267168015 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15792 ≤ 494914267168014 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15792 : RowArithmetic 15792 (1077627598120606984527/1000000000000000000000000) (591234966020345217200537/1000000000000000000000000) (5349047697454083/1000000000000000000000000) where
  r0 := (20155997153/40000000000000000)
  k0 := (1677957345199719/500000000000000000)
  k6 := (2724093920915651/250000000000000000)
  q := (44429719783046122651/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15792]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15792]

theorem width_15793 : mW 15793 = 495023964296307 := by
  have hu : mW 15793 ≤ 495023964296307 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15793 ≤ 495023964296306 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15793 : RowArithmetic 15793 (1077606580833660564337/1000000000000000000000000) (23649040084156944401949/40000000000000000000000) (668521172170799/125000000000000000000000) where
  r0 := (251926034889/500000000000000000)
  k0 := (3355755318782689/1000000000000000000)
  k6 := (2724007675837321/250000000000000000)
  q := (44431126476829281489/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15793]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15793]

theorem width_15794 : mW 15794 = 495133678790807 := by
  have hu : mW 15794 ≤ 495133678790807 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15794 ≤ 495133678790806 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15794 : RowArithmetic 15794 (1077585567986487164859/1000000000000000000000000) (591217039296683723440527/1000000000000000000000000) (2673645629455673/500000000000000000000000) where
  r0 := (251902109153/500000000000000000)
  k0 := (3355595964823403/1000000000000000000)
  k6 := (10895685755800219/1000000000000000000)
  q := (177730132504311153457/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15794]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15794]

theorem width_15795 : mW 15795 = 495243410653165 := by
  have hu : mW 15795 ≤ 495243410653165 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15795 ≤ 495243410653164 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15795 : RowArithmetic 15795 (134695569947232308087/125000000000000000000000) (36950504849900382644233/62500000000000000000000) (2673206671014751/500000000000000000000000) where
  r0 := (62969546801/125000000000000000)
  k0 := (1677718314260383/500000000000000000)
  k6 := (680958802563139/62500000000000000)
  q := (177735758923183491157/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15795]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15795]

theorem width_15796 : mW 15796 = 495353159885030 := by
  have hu : mW 15796 ≤ 495353159885030 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15796 ≤ 495353159885029 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15796 : RowArithmetic 15796 (538771777803273433737/500000000000000000000000) (59119911700887147859381/100000000000000000000000) (668191953332681/125000000000000000000000) where
  r0 := (503708538083/1000000000000000000)
  k0 := (1677638654936981/500000000000000000)
  k6 := (2178999191794823/200000000000000000)
  q := (17774138516395105443/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15796]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15796]

theorem width_15797 : mW 15797 = 495462926488052 := by
  have hu : mW 15797 ≤ 495462926488052 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15797 ≤ 495462926488051 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15797 : RowArithmetic 15797 (538761278035662460727/500000000000000000000000) (591190157527860512582023/1000000000000000000000000) (5344658112747787/1000000000000000000000000) where
  r0 := (503660709327/1000000000000000000)
  k0 := (671023601774437/200000000000000000)
  k6 := (2723662777421677/250000000000000000)
  q := (17774701122663075597/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15797]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15797]

theorem width_15798 : mW 15798 = 495572710463881 := by
  have hu : mW 15798 ≤ 495572710463881 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15798 ≤ 495572710463880 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15798 : RowArithmetic 15798 (269375390242741402397/250000000000000000000000) (295590599577577016948247/500000000000000000000000) (5343780800229141/1000000000000000000000000) where
  r0 := (25180644407/50000000000000000)
  k0 := (1677479362758973/500000000000000000)
  k6 := (544715314657141/50000000000000000)
  q := (44438159277809876449/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15798]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15798]

theorem width_15799 : mW 15799 = 495682511814165 := by
  have hu : mW 15799 ≤ 495682511814165 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15799 ≤ 495682511814164 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15799 : RowArithmetic 15799 (538740285152121464273/500000000000000000000000) (2364688967562131295373/4000000000000000000000) (213716147561847/40000000000000000000000) where
  r0 := (503565074521/1000000000000000000)
  k0 := (335479945981043/100000000000000000)
  k6 := (1089396150933727/100000000000000000)
  q := (177758262817794211251/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15799]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15799]

theorem width_15800 : mW 15800 = 495792330540556 := by
  have hu : mW 15800 ≤ 495792330540556 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15800 ≤ 495792330540555 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15800 : RowArithmetic 15800 (134682448008741268801/125000000000000000000000) (147790821433444455969491/250000000000000000000000) (333876673696221/62500000000000000000000) where
  r0 := (251758634233/500000000000000000)
  k0 := (419330026467353/125000000000000000)
  k6 := (10893616758264877/1000000000000000000)
  q := (88881944173155888501/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15800]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15800]

theorem width_15801 : mW 15801 = 495902166644702 := by
  have hu : mW 15801 ≤ 495902166644702 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15801 ≤ 495902166644701 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15801 : RowArithmetic 15801 (269359650566700534951/250000000000000000000000) (118230866136933991174449/200000000000000000000000) (1335287517612483/250000000000000000000000) where
  r0 := (20138778799/40000000000000000)
  k0 := (3354480981305641/1000000000000000000)
  k6 := (680829502495029/62500000000000000)
  q := (88884756848404552521/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15801]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15801]

theorem width_15802 : mW 15802 = 496012020128253 := by
  have hu : mW 15802 ≤ 496012020128253 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15802 ≤ 496012020128252 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15802 : RowArithmetic 15802 (1077417624893633615817/1000000000000000000000000) (295572688371495145738447/500000000000000000000000) (213610942516723/40000000000000000000000) where
  r0 := (503421679047/1000000000000000000)
  k0 := (167716088425503/50000000000000000)
  k6 := (10892927354298851/1000000000000000000)
  q := (177775138869303094689/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15802]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15802]

theorem width_15803 : mW 15803 = 496121890992859 := by
  have hu : mW 15803 ≤ 496121890992859 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15803 ≤ 496121890992858 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15803 : RowArithmetic 15803 (1077396651949199731227/1000000000000000000000000) (118227284781703967432267/200000000000000000000000) (667424657060587/125000000000000000000000) where
  r0 := (251686947839/500000000000000000)
  k0 := (1677081286670633/500000000000000000)
  k6 := (5446291350697431/500000000000000000)
  q := (177780763863810642589/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15803]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15803]

theorem width_15804 : mW 15804 = 496231779240171 := by
  have hu : mW 15804 ≤ 496231779240171 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15804 ≤ 496231779240170 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15804 : RowArithmetic 15804 (1077375683432275783229/1000000000000000000000000) (14778186804525994979903/25000000000000000000000) (5338521151090539/1000000000000000000000000) where
  r0 := (125831529967/250000000000000000)
  k0 := (335400339580177/100000000000000000)
  k6 := (10892238081203321/1000000000000000000)
  q := (177786388680348642713/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15804]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15804]

theorem width_15805 : mW 15805 = 496341684871838 := by
  have hu : mW 15805 ≤ 496341684871838 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15805 ≤ 496341684871837 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15805 : RowArithmetic 15805 (1077354719341638080697/1000000000000000000000000) (14777963039008283077763/25000000000000000000000) (5337645246676391/1000000000000000000000000) where
  r0 := (100655670323/200000000000000000)
  k0 := (3353844235887417/1000000000000000000)
  k6 := (5445946746859527/500000000000000000)
  q := (177792013318933986361/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15805]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15805]

theorem width_15806 : mW 15806 = 496451607889510 := by
  have hu : mW 15806 ≤ 496451607889510 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15806 ≤ 496451607889509 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15806 : RowArithmetic 15806 (1077333759676063076307/1000000000000000000000000) (118221914409235135820619/200000000000000000000000) (5336769543183049/1000000000000000000000000) where
  r0 := (251615295459/500000000000000000)
  k0 := (670737018719477/200000000000000000)
  k6 := (1361443617367111/125000000000000000)
  q := (177797637779583562161/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15806]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15806]

theorem width_15807 : mW 15807 = 496561548294837 := by
  have hu : mW 15807 ≤ 496561548294837 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15807 ≤ 496561548294836 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15807 : RowArithmetic 15807 (1077312804434327655643/1000000000000000000000000) (591100623638354164932463/1000000000000000000000000) (2667947020275667/500000000000000000000000) where
  r0 := (251591418887/500000000000000000)
  k0 := (1676762984462093/500000000000000000)
  k6 := (10891204416851651/1000000000000000000)
  q := (177803262062314256069/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15807]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15807]

theorem width_15808 : mW 15808 = 496671506089469 := by
  have hu : mW 15808 ≤ 496671506089469 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15808 ≤ 496671506089468 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15808 : RowArithmetic 15808 (107729185361520913699/100000000000000000000000) (591091676336648185438539/1000000000000000000000000) (2667509369361043/500000000000000000000000) where
  r0 := (503135092181/1000000000000000000)
  k0 := (3353366861863663/1000000000000000000)
  k6 := (1089085992745817/100000000000000000)
  q := (44452221541785737843/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15808]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15808]

theorem width_15809 : mW 15809 = 496781481275057 := by
  have hu : mW 15809 ≤ 496781481275057 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15809 ≤ 496781481275056 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15809 : RowArithmetic 15809 (16832357925273202853/15625000000000000000000) (59108273014083914635959/100000000000000000000000) (5334143637636159/1000000000000000000000000) where
  r0 := (25154367707/50000000000000000)
  k0 := (419150971552707/125000000000000000)
  k6 := (10890515470751277/1000000000000000000)
  q := (35562902018817305737/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15809]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15809]

theorem width_15810 : mW 15810 = 496891473853250 := by
  have hu : mW 15810 ≤ 496891473853250 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15810 ≤ 496891473853249 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15810 : RowArithmetic 15810 (269312491309983416079/250000000000000000000000) (295536892525354274392527/500000000000000000000000) (333329296077153/62500000000000000000000) where
  r0 := (251519811823/500000000000000000)
  k0 := (419131087573001/125000000000000000)
  k6 := (10890171046725803/1000000000000000000)
  q := (35564026768632373191/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15810]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15810]

theorem width_15811 : mW 15811 = 497001483825700 := by
  have hu : mW 15811 ≤ 497001483825700 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15811 ≤ 497001483825699 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15811 : RowArithmetic 15811 (538614513840666610349/500000000000000000000000) (118212968213207593968719/200000000000000000000000) (5332394037457839/1000000000000000000000000) where
  r0 := (5029919007/10000000000000000)
  k0 := (1676444823178279/500000000000000000)
  k6 := (10889826655376581/1000000000000000000)
  q := (8891287870719291923/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15811]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15811]

theorem width_15812 : mW 15812 = 497111511194056 := by
  have hu : mW 15812 ≤ 497111511194056 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15812 ≤ 497111511194055 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15812 : RowArithmetic 15812 (1077208094540462987737/1000000000000000000000000) (295527949093304489438671/500000000000000000000000) (666439942280909/125000000000000000000000) where
  r0 := (502944185299/1000000000000000000)
  k0 := (3352730609731813/1000000000000000000)
  k6 := (10889482296698443/1000000000000000000)
  q := (17783138080777531881/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15812]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15812]

theorem width_15813 : mW 15813 = 497221555959969 := by
  have hu : mW 15813 ≤ 497221555959969 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15813 ≤ 497221555959968 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15813 : RowArithmetic 15813 (107718716581610215647/100000000000000000000000) (591046956412203241836027/1000000000000000000000000) (2665322619771843/500000000000000000000000) where
  r0 := (502896477441/1000000000000000000)
  k0 := (3352571590705611/1000000000000000000)
  k6 := (680571123167889/62500000000000000)
  q := (35567400804669435389/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15813]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15813]

theorem width_15814 : mW 15814 = 497331618125089 := by
  have hu : mW 15814 ≤ 497331618125089 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15814 ≤ 497331618125088 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15814 : RowArithmetic 15814 (1077166241507030637897/1000000000000000000000000) (591038015742602527332371/1000000000000000000000000) (5329771141288053/1000000000000000000000000) where
  r0 := (251424388563/500000000000000000)
  k0 := (1676206294640229/500000000000000000)
  k6 := (10888793677334761/1000000000000000000)
  q := (88921313530559140071/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15814]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15814]

theorem width_15815 : mW 15815 = 497441697691066 := by
  have hu : mW 15815 ≤ 497441697691066 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15815 ≤ 497441697691065 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15815 : RowArithmetic 15815 (1077145321612028774341/1000000000000000000000000) (591029076177588588705253/1000000000000000000000000) (5328897243421369/1000000000000000000000000) where
  r0 := (502801084351/1000000000000000000)
  k0 := (419031700681107/125000000000000000)
  k6 := (1088844941663889/100000000000000000)
  q := (177848249921105493009/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15815]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15815]

theorem width_15816 : mW 15816 = 497551794659552 := by
  have hu : mW 15816 ≤ 497551794659552 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15816 ≤ 497551794659551 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15816 : RowArithmetic 15816 (1077124406129876763631/1000000000000000000000000) (591020137716943327520339/1000000000000000000000000) (5328023545884627/1000000000000000000000000) where
  r0 := (251376699557/500000000000000000)
  k0 := (3352094639206641/1000000000000000000)
  k6 := (10888105188593449/1000000000000000000)
  q := (177853872603325677487/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15816]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15816]

theorem width_15817 : mW 15817 = 497661909032197 := by
  have hu : mW 15817 ≤ 497661909032197 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15817 ≤ 497661909032196 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15817 : RowArithmetic 15817 (43084139802374232431/40000000000000000000000) (73876400045056073966673/125000000000000000000000) (1065430009723773/200000000000000000000000) where
  r0 := (251352860707/500000000000000000)
  k0 := (3351935690552983/1000000000000000000)
  k6 := (5443880496596639/500000000000000000)
  q := (35571899021559138571/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15817]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15817]

theorem width_15818 : mW 15818 = 497772040810651 := by
  have hu : mW 15818 ≤ 497772040810651 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15818 ≤ 497772040810650 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15818 : RowArithmetic 15818 (1077082588399247551513/1000000000000000000000000) (295501132053943170443967/500000000000000000000000) (2663138375782571/500000000000000000000000) where
  r0 := (502658051249/1000000000000000000)
  k0 := (670355351896743/200000000000000000)
  k6 := (170115887975519/15625000000000000)
  q := (44466279358633098931/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15818]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15818]

theorem width_15819 : mW 15819 = 497882189996565 := by
  have hu : mW 15819 ≤ 497882189996565 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15819 ≤ 497882189996564 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15819 : RowArithmetic 15819 (538530843074166882313/500000000000000000000000) (590993328959038648615137/1000000000000000000000000) (532540365466453/100000000000000000000000) where
  r0 := (251305194309/500000000000000000)
  k0 := (837904461499501/250000000000000000)
  k6 := (10887072700308107/1000000000000000000)
  q := (177870739583552640043/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15819]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15819]

theorem width_15820 : mW 15820 = 497992356591590 := by
  have hu : mW 15820 ≤ 497992356591590 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15820 ≤ 497992356591589 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15820 : RowArithmetic 15820 (538520394152698329827/500000000000000000000000) (590984394913687605782137/1000000000000000000000000) (5324530757858119/1000000000000000000000000) where
  r0 := (502562733519/1000000000000000000)
  k0 := (837864737522921/250000000000000000)
  k6 := (1360841075351599/125000000000000000)
  q := (177876361554873277097/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15820]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15820]

theorem width_15821 : mW 15821 = 498102540597377 := by
  have hu : mW 15821 ≤ 498102540597377 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15821 ≤ 498102540597376 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15821 : RowArithmetic 15821 (10770198948692188767/10000000000000000000000) (590975461971615288020061/1000000000000000000000000) (212946322443481/40000000000000000000000) where
  r0 := (10050301719/20000000000000000)
  k0 := (670260014352117/200000000000000000)
  k6 := (2177276907588423/200000000000000000)
  q := (44470495837127788877/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15821]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15821]

theorem width_15822 : mW 15822 = 498212742015577 := by
  have hu : mW 15822 ≤ 498212742015577 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15822 ≤ 498212742015576 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15822 : RowArithmetic 15822 (1076999005838583486233/1000000000000000000000000) (59096653013260396323601/100000000000000000000000) (5322785564292383/1000000000000000000000000) where
  r0 := (50246744591/100000000000000000)
  k0 := (3351141211003873/1000000000000000000)
  k6 := (272151012642273/25000000000000000)
  q := (35577520992896624247/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15822]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15822]

theorem width_15823 : mW 15823 = 498322960847840 := by
  have hu : mW 15823 ≤ 498322960847840 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15823 ≤ 498322960847839 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15823 : RowArithmetic 15823 (26924453030306856899/25000000000000000000000) (59095759939643587963071/100000000000000000000000) (16630978960673/3125000000000000000000) where
  r0 := (125604953349/250000000000000000)
  k0 := (1675491183907021/500000000000000000)
  k6 := (1360712063256757/125000000000000000)
  q := (177893226402806017577/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15823]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15823]

theorem width_15824 : mW 15824 = 498433197095817 := by
  have hu : mW 15824 ≤ 498433197095817 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15824 ≤ 498433197095816 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15824 : RowArithmetic 15824 (538478620494537588087/500000000000000000000000) (295474334881446666731397/500000000000000000000000) (332565073149821/62500000000000000000000) where
  r0 := (62796523551/125000000000000000)
  k0 := (3350823542193591/1000000000000000000)
  k6 := (10885352539026367/1000000000000000000)
  q := (177898847663496685169/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15824]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15824]

theorem width_15825 : mW 15825 = 498543450761160 := by
  have hu : mW 15825 ≤ 498543450761160 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15825 ≤ 498543450761159 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15825 : RowArithmetic 15825 (215387273033554052017/200000000000000000000000) (36933733826984917823031/62500000000000000000000) (5320169273178901/1000000000000000000000000) where
  r0 := (502324570943/1000000000000000000)
  k0 := (837666183533753/250000000000000000)
  k6 := (10885008604602703/1000000000000000000)
  q := (177904468746571961989/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15825]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15825]

theorem width_15826 : mW 15826 = 498653721845519 := by
  have hu : mW 15826 ≤ 498653721845519 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15826 ≤ 498653721845518 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15826 : RowArithmetic 15826 (269228873436786151103/250000000000000000000000) (590930813802814419828517/1000000000000000000000000) (41557012310171/7812500000000000000000) where
  r0 := (502276961001/1000000000000000000)
  k0 := (837626485910201/250000000000000000)
  k6 := (5442332351388957/500000000000000000)
  q := (22238761206506085419/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15826]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15826]

theorem width_15827 : mW 15827 = 498764010350546 := by
  have hu : mW 15827 ≤ 498764010350546 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15827 ≤ 498764010350545 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15827 : RowArithmetic 15827 (1076894626725983141539/1000000000000000000000000) (590921887475843055660299/1000000000000000000000000) (531842607790733/100000000000000000000000) where
  r0 := (251114679289/500000000000000000)
  k0 := (3350347170700121/1000000000000000000)
  k6 := (217686416670937/20000000000000000)
  q := (35583142075988736383/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15827]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15827]

theorem width_15828 : mW 15828 = 498874316277892 := by
  have hu : mW 15828 ≤ 498874316277892 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15828 ≤ 498874316277891 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15828 : RowArithmetic 15828 (538436882051535760001/500000000000000000000000) (147728240562656771713699/250000000000000000000000) (5317554779736493/1000000000000000000000000) where
  r0 := (251090881837/500000000000000000)
  k0 := (3350188415315459/1000000000000000000)
  k6 := (5441988498452181/500000000000000000)
  q := (44480332732568446919/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15828]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15828]

theorem width_15829 : mW 15829 = 498984639629208 := by
  have hu : mW 15829 ≤ 498984639629208 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15829 ≤ 498984639629207 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15829 : RowArithmetic 15829 (538426452938597908663/500000000000000000000000) (29545201906347458962149/50000000000000000000000) (1063336736226133/200000000000000000000000) where
  r0 := (502134176287/1000000000000000000)
  k0 := (1675014838741321/500000000000000000)
  k6 := (2176726638569061/200000000000000000)
  q := (88963475651527913987/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15829]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15829]

theorem width_15830 : mW 15830 = 499094980406145 := by
  have hu : mW 15830 ≤ 499094980406145 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15830 ≤ 499094980406144 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15830 : RowArithmetic 15830 (1076832052047142539833/1000000000000000000000000) (590895115104591959715719/1000000000000000000000000) (5315812782031153/1000000000000000000000000) where
  r0 := (7845103069/15625000000000000)
  k0 := (334987095720083/100000000000000000)
  k6 := (10883289421364531/1000000000000000000)
  q := (44483142874576656873/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15830]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15830]

theorem width_15831 : mW 15831 = 499205338610355 := by
  have hu : mW 15831 ≤ 499205338610355 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15831 ≤ 499205338610354 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15831 : RowArithmetic 15831 (134601400326462292027/125000000000000000000000) (590886193183338204721473/1000000000000000000000000) (66436776029741/12500000000000000000000) where
  r0 := (251019512029/500000000000000000)
  k0 := (3349712254462509/1000000000000000000)
  k6 := (170046026288389/15625000000000000)
  q := (88969095758021504127/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15831]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15831]

theorem width_15832 : mW 15832 = 499315714243489 := by
  have hu : mW 15832 ≤ 499315714243489 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15832 ≤ 499315714243488 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15832 : RowArithmetic 15832 (538395178784825285057/500000000000000000000000) (590877272362970673949757/1000000000000000000000000) (1062814316423279/200000000000000000000000) where
  r0 := (501991459211/1000000000000000000)
  k0 := (6699107138527/2000000000000000)
  k6 := (10882601976117257/1000000000000000000)
  q := (17794381135628178963/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15832]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15832]

theorem width_15833 : mW 15833 = 499426107307198 := by
  have hu : mW 15833 ≤ 499426107307198 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15833 ≤ 499426107307197 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15833 : RowArithmetic 15833 (8614156135358296267/8000000000000000000000) (590868352643272216243943/1000000000000000000000000) (2656600640591937/500000000000000000000000) where
  r0 := (803110243/1600000000000000)
  k0 := (3349394901606297/1000000000000000000)
  k6 := (1088225830234047/100000000000000000)
  q := (177949431019039788331/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15833]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15833]

theorem width_15834 : mW 15834 = 499536517803134 := by
  have hu : mW 15834 ≤ 499536517803134 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15834 ≤ 499536517803133 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15834 : RowArithmetic 15834 (538374340330447829973/500000000000000000000000) (115402233207817539747/195312500000000000000) (2656165589761551/500000000000000000000000) where
  r0 := (31368522003/62500000000000000)
  k0 := (1674618125743359/500000000000000000)
  k6 := (2176382932224279/200000000000000000)
  q := (11122190656520863651/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15834]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15834]

theorem width_15835 : mW 15835 = 499646945732949 := by
  have hu : mW 15835 ≤ 499646945732949 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15835 ≤ 499646945732948 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15835 : RowArithmetic 15835 (1076727848791764812009/1000000000000000000000000) (295425258252507164445581/500000000000000000000000) (1327865319268871/250000000000000000000000) where
  r0 := (1960346913/3906250000000000)
  k0 := (418634702362573/125000000000000000)
  k6 := (2720392763113723/250000000000000000)
  q := (177960669812180691287/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15835]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15835]

theorem width_15836 : mW 15836 = 499757391098293 := by
  have hu : mW 15836 ≤ 499757391098293 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15836 ≤ 499757391098292 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15836 : RowArithmetic 15836 (269176755327795962799/250000000000000000000000) (118168320017204172320673/200000000000000000000000) (531059157378247/100000000000000000000000) where
  r0 := (501801274913/1000000000000000000)
  k0 := (3348919003843711/1000000000000000000)
  k6 := (544061373816791/50000000000000000)
  q := (44491572235649303923/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15836]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15836]

theorem width_15837 : mW 15837 = 499867853900820 := by
  have hu : mW 15837 ≤ 499867853900820 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15837 ≤ 499867853900819 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15837 : RowArithmetic 15837 (1076686198217941423751/1000000000000000000000000) (118166536953365697285813/200000000000000000000000) (331857629349093/62500000000000000000000) where
  r0 := (501753747601/1000000000000000000)
  k0 := (3348760406311917/1000000000000000000)
  k6 := (10880883932759043/1000000000000000000)
  q := (177971907895600197727/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15837]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15837]

theorem width_15838 : mW 15838 = 499978334142180 := by
  have hu : mW 15838 ≤ 499978334142180 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15838 ≤ 499978334142179 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15838 : RowArithmetic 15838 (1076665379510827746381/1000000000000000000000000) (118164754109444071635287/200000000000000000000000) (530885276442603/100000000000000000000000) where
  r0 := (31356639237/62500000000000000)
  k0 := (3348601826307691/1000000000000000000)
  k6 := (85004222044683/7812500000000000)
  q := (88988763335603220417/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15838]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15838]

theorem width_15839 : mW 15839 = 500088831824025 := by
  have hu : mW 15839 ≤ 500088831824025 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15839 ≤ 500088831824024 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15839 : RowArithmetic 15839 (1076644565188632891633/1000000000000000000000000) (295407428713489806591967/500000000000000000000000) (530798365824559/100000000000000000000000) where
  r0 := (501658715483/1000000000000000000)
  k0 := (418555407977939/125000000000000000)
  k6 := (5440098471605913/500000000000000000)
  q := (88991572634716372901/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15839]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15839]

theorem width_15840 : mW 15840 = 500199346948006 := by
  have hu : mW 15840 ≤ 500199346948006 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15840 ≤ 500199346948005 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15840 : RowArithmetic 15840 (215324751050029528919/200000000000000000000000) (590805945405889600726163/1000000000000000000000000) (5307114750985693/1000000000000000000000000) where
  r0 := (501611210673/1000000000000000000)
  k0 := (3348284718858531/1000000000000000000)
  k6 := (2175970699446223/200000000000000000)
  q := (17798876369029591077/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15840]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15840]

theorem width_15841 : mW 15841 = 500309879515777 := by
  have hu : mW 15841 ≤ 500309879515777 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15841 ≤ 500309879515776 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15841 : RowArithmetic 15841 (107660294969416236147/100000000000000000000000) (590797034483733591203587/1000000000000000000000000) (5306246042587851/1000000000000000000000000) where
  r0 := (501563713359/1000000000000000000)
  k0 := (418515773925653/125000000000000000)
  k6 := (10879510083772159/1000000000000000000)
  q := (22249297741726591403/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15841]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15841]

theorem width_15842 : mW 15842 = 500420429528988 := by
  have hu : mW 15842 ≤ 500420429528988 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15842 ≤ 500420429528987 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15842 : RowArithmetic 15842 (53829107425973448323/50000000000000000000000) (147697031165073744558949/250000000000000000000000) (1061075506598729/200000000000000000000000) where
  r0 := (501516223541/1000000000000000000)
  k0 := (3347967681466079/1000000000000000000)
  k6 := (10879166702829823/1000000000000000000)
  q := 178
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15842]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15842]

theorem width_15843 : mW 15843 = 500530996989292 := by
  have hu : mW 15843 ≤ 500530996989292 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15843 ≤ 500530996989291 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15843 : RowArithmetic 15843 (538280675862429477349/500000000000000000000000) (590779215935357206020229/1000000000000000000000000) (5304509222144643/1000000000000000000000000) where
  r0 := (501468741217/1000000000000000000)
  k0 := (3347809189036907/1000000000000000000)
  k6 := (5439411677199489/500000000000000000)
  q := (89002808944437253643/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15843]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15843]

theorem width_15844 : mW 15844 = 500641581898341 := by
  have hu : mW 15844 ≤ 500641581898341 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15844 ≤ 500641581898340 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15844 : RowArithmetic 15844 (538270279654562266541/500000000000000000000000) (590770308308703780040871/1000000000000000000000000) (1325910277495611/250000000000000000000000) where
  r0 := (100284253277/200000000000000000)
  k0 := (3347650714113519/1000000000000000000)
  k6 := (5439240019237247/500000000000000000)
  q := (178011235600453040617/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15844]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15844]

theorem width_15845 : mW 15845 = 500752184257786 := by
  have hu : mW 15845 ≤ 500752184257786 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15845 ≤ 500752184257785 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15845 : RowArithmetic 15845 (215303954254211723911/200000000000000000000000) (36922587611257388268867/62500000000000000000000) (5302773196448681/1000000000000000000000000) where
  r0 := (501373799043/1000000000000000000)
  k0 := (836873064172931/250000000000000000)
  k6 := (271953418876281/25000000000000000)
  q := (89008426567376192441/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15845]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15845]

theorem width_15846 : mW 15846 = 500862804069280 := by
  have hu : mW 15846 ≤ 500862804069280 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15846 ≤ 500862804069279 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15846 : RowArithmetic 15846 (1076498987609453988421/1000000000000000000000000) (590752496349384204149277/1000000000000000000000000) (5301905481484987/1000000000000000000000000) where
  r0 := (50132633919/100000000000000000)
  k0 := (334733381677067/100000000000000000)
  k6 := (10877793504124091/1000000000000000000)
  q := (178022470491789322321/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15846]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15846]

theorem width_15847 : mW 15847 = 500973441334475 := by
  have hu : mW 15847 ≤ 500973441334475 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15847 ≤ 500973441334474 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15847 : RowArithmetic 15847 (269119552080776031213/250000000000000000000000) (3692147450101783345753/6250000000000000000000) (5301037965033027/1000000000000000000000000) where
  r0 := (501278886823/1000000000000000000)
  k0 := (1673587697171413/500000000000000000)
  k6 := (5438725142843959/500000000000000000)
  q := (44507021917895158131/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15847]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15847]

theorem width_15848 : mW 15848 = 501084096055023 := by
  have hu : mW 15848 ≤ 501084096055023 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15848 ≤ 501084096055022 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15848 : RowArithmetic 15848 (26911435835270073493/25000000000000000000000) (118146937756121075255169/200000000000000000000000) (5300170647034487/1000000000000000000000000) where
  r0 := (501231441943/1000000000000000000)
  k0 := (669403397882803/200000000000000000)
  k6 := (5438553549868799/500000000000000000)
  q := (178033704674143092439/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15848]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15848]

theorem width_15849 : mW 15849 = 501194768232576 := by
  have hu : mW 15849 ≤ 501194768232576 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15849 ≤ 501194768232575 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15849 : RowArithmetic 15849 (538218331435672384703/500000000000000000000000) (590725786642128118918899/1000000000000000000000000) (211972141097243/40000000000000000000000) where
  r0 := (250592002273/500000000000000000)
  k0 := (836714650493341/250000000000000000)
  k6 := (2719190986567001/250000000000000000)
  q := (89019660749746738181/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15849]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15849]

theorem width_15850 : mW 15850 = 501305457868787 := by
  have hu : mW 15850 ≤ 501305457868787 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15850 ≤ 501305457868786 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15850 : RowArithmetic 15850 (1076415896703524091369/1000000000000000000000000) (590716885600637426299343/1000000000000000000000000) (5298436606164509/1000000000000000000000000) where
  r0 := (501136574631/1000000000000000000)
  k0 := (167335011601001/50000000000000000)
  k6 := (5438210412637007/500000000000000000)
  q := (89022469073824277973/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15850]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15850]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 15776 then ⟨(538982239762338498237/500000000000000000000000), (18480579365970767474437/31250000000000000000000), (5363128289480121/1000000000000000000000000)⟩ else
  if n = 15777 then ⟨(269485847758497678947/250000000000000000000000), (295684779008924252163167/500000000000000000000000), (536224673516923/100000000000000000000000)⟩ else
  if n = 15778 then ⟨(538961153501392472553/500000000000000000000000), (147840144359333181348377/250000000000000000000000), (2680682691722441/500000000000000000000000)⟩ else
  if n = 15779 then ⟨(67368826714364078449/62500000000000000000000), (591351597969296805473891/1000000000000000000000000), (1340121058561829/250000000000000000000000)⟩ else
  if n = 15780 then ⟨(1077880152313876778829/1000000000000000000000000), (591342619613520464330997/1000000000000000000000000), (1339900821879189/250000000000000000000000)⟩ else
  if n = 15781 then ⟨(53892954082685283501/50000000000000000000000), (295666821184891752709069/500000000000000000000000), (214348901727739/40000000000000000000000)⟩ else
  if n = 15782 then ⟨(107783801544807822833/100000000000000000000000), (295662333118932824733373/500000000000000000000000), (669730250152219/125000000000000000000000)⟩ else
  if n = 15783 then ⟨(107781695369576119059/100000000000000000000000), (591315691217546856941591/1000000000000000000000000), (1339240415382473/250000000000000000000000)⟩ else
  if n = 15784 then ⟨(8420280440590013521/7812500000000000000000), (591306717308607067443937/1000000000000000000000000), (267804076203511/50000000000000000000000)⟩ else
  if n = 15785 then ⟨(13472185544326596881/12500000000000000000000), (147824436127706572006543/250000000000000000000000), (1071040317755819/200000000000000000000000)⟩ else
  if n = 15786 then ⟨(538876897573173503021/500000000000000000000000), (295644386411992264209271/500000000000000000000000), (1713382993791/320000000000000000000)⟩ else
  if n = 15787 then ⟨(1077732751194947981233/1000000000000000000000000), (147819950561965487784523/250000000000000000000000), (5353442324463953/1000000000000000000000000)⟩ else
  if n = 15788 then ⟨(1077711711690699886957/1000000000000000000000000), (591270832782238758237141/1000000000000000000000000), (334535187207547/62500000000000000000000)⟩ else
  if n = 15789 then ⟨(538845338316185894191/500000000000000000000000), (591261864426895139620933/1000000000000000000000000), (2675841934053849/500000000000000000000000)⟩ else
  if n = 15790 then ⟨(538834823009366738769/500000000000000000000000), (295626448590805716810483/500000000000000000000000), (5350804942765249/1000000000000000000000000)⟩ else
  if n = 15791 then ⟨(269412154962138722911/250000000000000000000000), (59124393104616800476407/100000000000000000000000), (5349926219233873/1000000000000000000000000)⟩ else
  if n = 15792 then ⟨(1077627598120606984527/1000000000000000000000000), (591234966020345217200537/1000000000000000000000000), (5349047697454083/1000000000000000000000000)⟩ else
  if n = 15793 then ⟨(1077606580833660564337/1000000000000000000000000), (23649040084156944401949/40000000000000000000000), (668521172170799/125000000000000000000000)⟩ else
  if n = 15794 then ⟨(1077585567986487164859/1000000000000000000000000), (591217039296683723440527/1000000000000000000000000), (2673645629455673/500000000000000000000000)⟩ else
  if n = 15795 then ⟨(134695569947232308087/125000000000000000000000), (36950504849900382644233/62500000000000000000000), (2673206671014751/500000000000000000000000)⟩ else
  if n = 15796 then ⟨(538771777803273433737/500000000000000000000000), (59119911700887147859381/100000000000000000000000), (668191953332681/125000000000000000000000)⟩ else
  if n = 15797 then ⟨(538761278035662460727/500000000000000000000000), (591190157527860512582023/1000000000000000000000000), (5344658112747787/1000000000000000000000000)⟩ else
  if n = 15798 then ⟨(269375390242741402397/250000000000000000000000), (295590599577577016948247/500000000000000000000000), (5343780800229141/1000000000000000000000000)⟩ else
  if n = 15799 then ⟨(538740285152121464273/500000000000000000000000), (2364688967562131295373/4000000000000000000000), (213716147561847/40000000000000000000000)⟩ else
  if n = 15800 then ⟨(134682448008741268801/125000000000000000000000), (147790821433444455969491/250000000000000000000000), (333876673696221/62500000000000000000000)⟩ else
  if n = 15801 then ⟨(269359650566700534951/250000000000000000000000), (118230866136933991174449/200000000000000000000000), (1335287517612483/250000000000000000000000)⟩ else
  if n = 15802 then ⟨(1077417624893633615817/1000000000000000000000000), (295572688371495145738447/500000000000000000000000), (213610942516723/40000000000000000000000)⟩ else
  if n = 15803 then ⟨(1077396651949199731227/1000000000000000000000000), (118227284781703967432267/200000000000000000000000), (667424657060587/125000000000000000000000)⟩ else
  if n = 15804 then ⟨(1077375683432275783229/1000000000000000000000000), (14778186804525994979903/25000000000000000000000), (5338521151090539/1000000000000000000000000)⟩ else
  if n = 15805 then ⟨(1077354719341638080697/1000000000000000000000000), (14777963039008283077763/25000000000000000000000), (5337645246676391/1000000000000000000000000)⟩ else
  if n = 15806 then ⟨(1077333759676063076307/1000000000000000000000000), (118221914409235135820619/200000000000000000000000), (5336769543183049/1000000000000000000000000)⟩ else
  if n = 15807 then ⟨(1077312804434327655643/1000000000000000000000000), (591100623638354164932463/1000000000000000000000000), (2667947020275667/500000000000000000000000)⟩ else
  if n = 15808 then ⟨(107729185361520913699/100000000000000000000000), (591091676336648185438539/1000000000000000000000000), (2667509369361043/500000000000000000000000)⟩ else
  if n = 15809 then ⟨(16832357925273202853/15625000000000000000000), (59108273014083914635959/100000000000000000000000), (5334143637636159/1000000000000000000000000)⟩ else
  if n = 15810 then ⟨(269312491309983416079/250000000000000000000000), (295536892525354274392527/500000000000000000000000), (333329296077153/62500000000000000000000)⟩ else
  if n = 15811 then ⟨(538614513840666610349/500000000000000000000000), (118212968213207593968719/200000000000000000000000), (5332394037457839/1000000000000000000000000)⟩ else
  if n = 15812 then ⟨(1077208094540462987737/1000000000000000000000000), (295527949093304489438671/500000000000000000000000), (666439942280909/125000000000000000000000)⟩ else
  if n = 15813 then ⟨(107718716581610215647/100000000000000000000000), (591046956412203241836027/1000000000000000000000000), (2665322619771843/500000000000000000000000)⟩ else
  if n = 15814 then ⟨(1077166241507030637897/1000000000000000000000000), (591038015742602527332371/1000000000000000000000000), (5329771141288053/1000000000000000000000000)⟩ else
  if n = 15815 then ⟨(1077145321612028774341/1000000000000000000000000), (591029076177588588705253/1000000000000000000000000), (5328897243421369/1000000000000000000000000)⟩ else
  if n = 15816 then ⟨(1077124406129876763631/1000000000000000000000000), (591020137716943327520339/1000000000000000000000000), (5328023545884627/1000000000000000000000000)⟩ else
  if n = 15817 then ⟨(43084139802374232431/40000000000000000000000), (73876400045056073966673/125000000000000000000000), (1065430009723773/200000000000000000000000)⟩ else
  if n = 15818 then ⟨(1077082588399247551513/1000000000000000000000000), (295501132053943170443967/500000000000000000000000), (2663138375782571/500000000000000000000000)⟩ else
  if n = 15819 then ⟨(538530843074166882313/500000000000000000000000), (590993328959038648615137/1000000000000000000000000), (532540365466453/100000000000000000000000)⟩ else
  if n = 15820 then ⟨(538520394152698329827/500000000000000000000000), (590984394913687605782137/1000000000000000000000000), (5324530757858119/1000000000000000000000000)⟩ else
  if n = 15821 then ⟨(10770198948692188767/10000000000000000000000), (590975461971615288020061/1000000000000000000000000), (212946322443481/40000000000000000000000)⟩ else
  if n = 15822 then ⟨(1076999005838583486233/1000000000000000000000000), (59096653013260396323601/100000000000000000000000), (5322785564292383/1000000000000000000000000)⟩ else
  if n = 15823 then ⟨(26924453030306856899/25000000000000000000000), (59095759939643587963071/100000000000000000000000), (16630978960673/3125000000000000000000)⟩ else
  if n = 15824 then ⟨(538478620494537588087/500000000000000000000000), (295474334881446666731397/500000000000000000000000), (332565073149821/62500000000000000000000)⟩ else
  if n = 15825 then ⟨(215387273033554052017/200000000000000000000000), (36933733826984917823031/62500000000000000000000), (5320169273178901/1000000000000000000000000)⟩ else
  if n = 15826 then ⟨(269228873436786151103/250000000000000000000000), (590930813802814419828517/1000000000000000000000000), (41557012310171/7812500000000000000000)⟩ else
  if n = 15827 then ⟨(1076894626725983141539/1000000000000000000000000), (590921887475843055660299/1000000000000000000000000), (531842607790733/100000000000000000000000)⟩ else
  if n = 15828 then ⟨(538436882051535760001/500000000000000000000000), (147728240562656771713699/250000000000000000000000), (5317554779736493/1000000000000000000000000)⟩ else
  if n = 15829 then ⟨(538426452938597908663/500000000000000000000000), (29545201906347458962149/50000000000000000000000), (1063336736226133/200000000000000000000000)⟩ else
  if n = 15830 then ⟨(1076832052047142539833/1000000000000000000000000), (590895115104591959715719/1000000000000000000000000), (5315812782031153/1000000000000000000000000)⟩ else
  if n = 15831 then ⟨(134601400326462292027/125000000000000000000000), (590886193183338204721473/1000000000000000000000000), (66436776029741/12500000000000000000000)⟩ else
  if n = 15832 then ⟨(538395178784825285057/500000000000000000000000), (590877272362970673949757/1000000000000000000000000), (1062814316423279/200000000000000000000000)⟩ else
  if n = 15833 then ⟨(8614156135358296267/8000000000000000000000), (590868352643272216243943/1000000000000000000000000), (2656600640591937/500000000000000000000000)⟩ else
  if n = 15834 then ⟨(538374340330447829973/500000000000000000000000), (115402233207817539747/195312500000000000000), (2656165589761551/500000000000000000000000)⟩ else
  if n = 15835 then ⟨(1076727848791764812009/1000000000000000000000000), (295425258252507164445581/500000000000000000000000), (1327865319268871/250000000000000000000000)⟩ else
  if n = 15836 then ⟨(269176755327795962799/250000000000000000000000), (118168320017204172320673/200000000000000000000000), (531059157378247/100000000000000000000000)⟩ else
  if n = 15837 then ⟨(1076686198217941423751/1000000000000000000000000), (118166536953365697285813/200000000000000000000000), (331857629349093/62500000000000000000000)⟩ else
  if n = 15838 then ⟨(1076665379510827746381/1000000000000000000000000), (118164754109444071635287/200000000000000000000000), (530885276442603/100000000000000000000000)⟩ else
  if n = 15839 then ⟨(1076644565188632891633/1000000000000000000000000), (295407428713489806591967/500000000000000000000000), (530798365824559/100000000000000000000000)⟩ else
  if n = 15840 then ⟨(215324751050029528919/200000000000000000000000), (590805945405889600726163/1000000000000000000000000), (5307114750985693/1000000000000000000000000)⟩ else
  if n = 15841 then ⟨(107660294969416236147/100000000000000000000000), (590797034483733591203587/1000000000000000000000000), (5306246042587851/1000000000000000000000000)⟩ else
  if n = 15842 then ⟨(53829107425973448323/50000000000000000000000), (147697031165073744558949/250000000000000000000000), (1061075506598729/200000000000000000000000)⟩ else
  if n = 15843 then ⟨(538280675862429477349/500000000000000000000000), (590779215935357206020229/1000000000000000000000000), (5304509222144643/1000000000000000000000000)⟩ else
  if n = 15844 then ⟨(538270279654562266541/500000000000000000000000), (590770308308703780040871/1000000000000000000000000), (1325910277495611/250000000000000000000000)⟩ else
  if n = 15845 then ⟨(215303954254211723911/200000000000000000000000), (36922587611257388268867/62500000000000000000000), (5302773196448681/1000000000000000000000000)⟩ else
  if n = 15846 then ⟨(1076498987609453988421/1000000000000000000000000), (590752496349384204149277/1000000000000000000000000), (5301905481484987/1000000000000000000000000)⟩ else
  if n = 15847 then ⟨(269119552080776031213/250000000000000000000000), (3692147450101783345753/6250000000000000000000), (5301037965033027/1000000000000000000000000)⟩ else
  if n = 15848 then ⟨(26911435835270073493/25000000000000000000000), (118146937756121075255169/200000000000000000000000), (5300170647034487/1000000000000000000000000)⟩ else
  if n = 15849 then ⟨(538218331435672384703/500000000000000000000000), (590725786642128118918899/1000000000000000000000000), (211972141097243/40000000000000000000000)⟩ else
  ⟨(1076415896703524091369/1000000000000000000000000), (590716885600637426299343/1000000000000000000000000), (5298436606164509/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15776 ≤ n) (hb : n ≤ 15850) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15776
  · exact row_15777
  · exact row_15778
  · exact row_15779
  · exact row_15780
  · exact row_15781
  · exact row_15782
  · exact row_15783
  · exact row_15784
  · exact row_15785
  · exact row_15786
  · exact row_15787
  · exact row_15788
  · exact row_15789
  · exact row_15790
  · exact row_15791
  · exact row_15792
  · exact row_15793
  · exact row_15794
  · exact row_15795
  · exact row_15796
  · exact row_15797
  · exact row_15798
  · exact row_15799
  · exact row_15800
  · exact row_15801
  · exact row_15802
  · exact row_15803
  · exact row_15804
  · exact row_15805
  · exact row_15806
  · exact row_15807
  · exact row_15808
  · exact row_15809
  · exact row_15810
  · exact row_15811
  · exact row_15812
  · exact row_15813
  · exact row_15814
  · exact row_15815
  · exact row_15816
  · exact row_15817
  · exact row_15818
  · exact row_15819
  · exact row_15820
  · exact row_15821
  · exact row_15822
  · exact row_15823
  · exact row_15824
  · exact row_15825
  · exact row_15826
  · exact row_15827
  · exact row_15828
  · exact row_15829
  · exact row_15830
  · exact row_15831
  · exact row_15832
  · exact row_15833
  · exact row_15834
  · exact row_15835
  · exact row_15836
  · exact row_15837
  · exact row_15838
  · exact row_15839
  · exact row_15840
  · exact row_15841
  · exact row_15842
  · exact row_15843
  · exact row_15844
  · exact row_15845
  · exact row_15846
  · exact row_15847
  · exact row_15848
  · exact row_15849
  · exact row_15850

end BstLean.Part271.R3.Rows15776
