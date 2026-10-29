import BstLean.Part291Rectangle
import BstLean.Part291Certificates1
import BstLean.Part291LocalEnergyBatch0
import BstLean.Part291LocalEnergyBatch1
namespace BstLean.BlueprintLow
open Real Set BstLean.Part255
noncomputable def lowRectangle1_0 : FrameRectangleCertificate 8250 8500 (23/50) (921/2000) lowTIParameters0 where
  full := (3374448303/31250000000)
  energy := (44267434443/62500000000)
  cov := (71122778493/250000000000)
  schur := (105002552837/100000000000)
  cap := (242252281/250000000000)
  W2 := (3673241806927/1000000000000)
  V := (36229717/125000000000)
  mass := (259407111/1000000000000)
  rootN := (102470753309/100000000000)
  rootB := (6225782277/200000000000)
  rootU := (629797798203/1000000000000)
  rootV := (3404924293/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_0.scalar_checked
  centre := fun n hn => lowFull1_0 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy0 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_0.bound (by norm_num) hn lowTIParameters0_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_1 : FrameRectangleCertificate 8250 8500 (921/2000) (461/1000) lowTIParameters1 where
  full := (2161306179/20000000000)
  energy := (708032000171/1000000000000)
  cov := (284673416909/1000000000000)
  schur := (65609288191/62500000000)
  cap := (38784233/40000000000)
  W2 := (3669889800233/1000000000000)
  V := (58004693/200000000000)
  mass := (245023833/1000000000000)
  rootN := (1024572404009/1000000000000)
  rootB := (3892311783/125000000000)
  rootU := (78719019211/125000000000)
  rootV := (17030075309/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_1.scalar_checked
  centre := fun n hn => lowFull1_1 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy1 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_1.bound (by norm_num) hn lowTIParameters1_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_2 : FrameRectangleCertificate 8250 8500 (461/1000) (923/2000) lowTIParameters2 where
  full := (54074204297/500000000000)
  energy := (353892583027/500000000000)
  cov := (14242776599/50000000000)
  schur := (1049471965781/1000000000000)
  cap := (485101189/500000000000)
  W2 := (3666545478511/1000000000000)
  V := (145104501/500000000000)
  mass := (232024899/1000000000000)
  rootN := (1024437389879/1000000000000)
  rootB := (31148071819/1000000000000)
  rootU := (629707121239/1000000000000)
  rootV := (17035521771/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_2.scalar_checked
  centre := fun n hn => lowFull1_2 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy2 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_2.bound (by norm_num) hn lowTIParameters2_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_3 : FrameRectangleCertificate 8250 8500 (923/2000) (231/500) lowTIParameters3 where
  full := (54115823303/500000000000)
  energy := (707538448651/1000000000000)
  cov := (8911357599/31250000000)
  schur := (262414753667/250000000000)
  cap := (60692633/62500000000)
  W2 := (457901101911/125000000000)
  V := (2905227/10000000000)
  mass := (220271951/1000000000000)
  rootN := (1024528679281/1000000000000)
  rootB := (31162190681/1000000000000)
  rootU := (629662704899/1000000000000)
  rootV := (8522363229/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_3.scalar_checked
  centre := fun n hn => lowFull1_3 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy3 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_3.bound (by norm_num) hn lowTIParameters3_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_4 : FrameRectangleCertificate 8250 8500 (231/500) (37/80) lowTIParameters4 where
  full := (54157512493/500000000000)
  energy := (707291847877/1000000000000)
  cov := (285219197789/1000000000000)
  schur := (1048919482807/1000000000000)
  cap := (6071219/6250000000)
  W2 := (1829939892139/500000000000)
  V := (290579503/1000000000000)
  mass := (41928193/200000000000)
  rootN := (512083851241/500000000000)
  rootB := (973975343/31250000000)
  rootU := (62961890877/100000000000)
  rootV := (17046392669/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_4.scalar_checked
  centre := fun n hn => lowFull1_4 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy4 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_4.bound (by norm_num) hn lowTIParameters4_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_5 : FrameRectangleCertificate 8250 8500 (37/80) (463/1000) lowTIParameters5 where
  full := (21679709151/200000000000)
  energy := (176761340913/250000000000)
  cov := (285526836757/1000000000000)
  schur := (52455330647/50000000000)
  cap := (972274709/1000000000000)
  W2 := (1828279179681/500000000000)
  V := (290892923/1000000000000)
  mass := (200020717/1000000000000)
  rootN := (512129527791/500000000000)
  rootB := (31181319873/1000000000000)
  rootU := (157393934251/250000000000)
  rootV := (17055583339/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_5.scalar_checked
  centre := fun n hn => lowFull1_5 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy5 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_5.bound (by norm_num) hn lowTIParameters5_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_6 : FrameRectangleCertificate 8250 8500 (463/1000) (927/2000) lowTIParameters6 where
  full := (108482210959/1000000000000)
  energy := (44174937243/62500000000)
  cov := (285582114037/1000000000000)
  schur := (41934723107/40000000000)
  cap := (194517431/200000000000)
  W2 := (228327782153/62500000000)
  V := (7273731/25000000000)
  mass := (19131141/100000000000)
  rootN := (511949235197/500000000000)
  rootB := (15593164809/500000000000)
  rootU := (125906638761/200000000000)
  rootV := (17057234243/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_6.scalar_checked
  centre := fun n hn => lowFull1_6 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy6 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_6.bound (by norm_num) hn lowTIParameters6_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_7 : FrameRectangleCertificate 8250 8500 (927/2000) (58/125) lowTIParameters7 where
  full := (21713204533/200000000000)
  energy := (141310548901/200000000000)
  cov := (4467023143/15625000000)
  schur := (1048555287141/1000000000000)
  cap := (243366691/250000000000)
  W2 := (364993822363/100000000000)
  V := (291262383/1000000000000)
  mass := (22927933/125000000000)
  rootN := (819191909/800000000)
  rootB := (7800107227/250000000000)
  rootU := (629491283429/1000000000000)
  rootV := (17066410959/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_7.scalar_checked
  centre := fun n hn => lowFull1_7 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy7 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_7.bound (by norm_num) hn lowTIParameters7_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_8 : FrameRectangleCertificate 8250 8500 (58/125) (929/2000) lowTIParameters8 where
  full := (108649982961/1000000000000)
  energy := (35315330471/50000000000)
  cov := (285944281079/1000000000000)
  schur := (65488608769/62500000000)
  cap := (486889381/500000000000)
  W2 := (1823319730583/500000000000)
  V := (291318213/1000000000000)
  mass := (17627643/100000000000)
  rootN := (20472593781/20000000000)
  rootB := (15602714203/500000000000)
  rootU := (78681251273/125000000000)
  rootV := (341360931/20000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_8.scalar_checked
  centre := fun n hn => lowFull1_8 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy8 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_8.bound (by norm_num) hn lowTIParameters8_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_9 : FrameRectangleCertificate 8250 8500 (929/2000) (93/200) lowTIParameters9 where
  full := (108734093963/1000000000000)
  energy := (353030295273/500000000000)
  cov := (286251376701/1000000000000)
  schur := (1048005027217/1000000000000)
  cap := (974658327/1000000000000)
  W2 := (3643348201271/1000000000000)
  V := (7290777/25000000000)
  mass := (169798031/1000000000000)
  rootN := (1023721166733/1000000000000)
  rootB := (15609759183/500000000000)
  rootU := (4917260769/7812500000)
  rootV := (8538604687/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_9.scalar_checked
  centre := fun n hn => lowFull1_9 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy9 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_9.bound (by norm_num) hn lowTIParameters9_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_10 : FrameRectangleCertificate 8250 8500 (93/200) (931/2000) lowTIParameters10 where
  full := (27204589451/250000000000)
  energy := (705814687803/1000000000000)
  cov := (286305699699/1000000000000)
  schur := (4189073849/4000000000)
  cap := (487484949/500000000000)
  W2 := (1820032209207/500000000000)
  V := (36460803/125000000000)
  mass := (163923297/1000000000000)
  rootN := (1023361354679/1000000000000)
  rootB := (31224507971/1000000000000)
  rootU := (629369392577/1000000000000)
  rootV := (17078829703/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_10.scalar_checked
  centre := fun n hn => lowFull1_10 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy10 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_10.bound (by norm_num) hn lowTIParameters10_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_11 : FrameRectangleCertificate 8250 8500 (931/2000) (233/500) lowTIParameters11 where
  full := (13612847081/125000000000)
  energy := (705568901107/1000000000000)
  cov := (8956641381/31250000000)
  schur := (1047455824751/1000000000000)
  cap := (975849441/1000000000000)
  W2 := (454598510897/125000000000)
  V := (58399803/200000000000)
  mass := (31718761/200000000000)
  rootN := (40938115731/40000000000)
  rootB := (31238588973/1000000000000)
  rootU := (39333128569/62500000000)
  rootV := (1708797867/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_11.scalar_checked
  centre := fun n hn => lowFull1_11 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy11 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_11.bound (by norm_num) hn lowTIParameters11_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_12 : FrameRectangleCertificate 8250 8500 (233/500) (933/2000) lowTIParameters12 where
  full := (4359494107/40000000000)
  energy := (88165403797/125000000000)
  cov := (57333274231/200000000000)
  schur := (26168005923/25000000000)
  cap := (488080303/500000000000)
  W2 := (1816759591083/500000000000)
  V := (146026937/500000000000)
  mass := (76878497/500000000000)
  rootN := (1023093464411/1000000000000)
  rootB := (6248713807/200000000000)
  rootU := (629291376517/1000000000000)
  rootV := (17089583787/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_12.scalar_checked
  centre := fun n hn => lowFull1_12 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy12 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_12.bound (by norm_num) hn lowTIParameters12_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_13 : FrameRectangleCertificate 8250 8500 (933/2000) (467/1000) lowTIParameters13 where
  full := (21814417619/200000000000)
  energy := (352538837763/500000000000)
  cov := (286972924877/1000000000000)
  schur := (1046907673149/1000000000000)
  cap := (977040149/1000000000000)
  W2 := (726051535639/200000000000)
  V := (292366189/1000000000000)
  mass := (37341389/250000000000)
  rootN := (511592531501/500000000000)
  rootB := (625152829/20000000000)
  rootU := (314626677701/500000000000)
  rootV := (17098718929/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_13.scalar_checked
  centre := fun n hn => lowFull1_13 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy13 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_13.bound (by norm_num) hn lowTIParameters13_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_14 : FrameRectangleCertificate 8250 8500 (467/1000) (187/400) lowTIParameters14 where
  full := (109156985139/1000000000000)
  energy := (704832236477/1000000000000)
  cov := (28702629667/100000000000)
  schur := (209234611527/200000000000)
  cap := (977350931/1000000000000)
  W2 := (362700355019/100000000000)
  V := (73105141/250000000000)
  mass := (145376893/1000000000000)
  rootN := (102282601533/100000000000)
  rootB := (31262612351/1000000000000)
  rootU := (157303999597/250000000000)
  rootV := (17100308887/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_14.scalar_checked
  centre := fun n hn => lowFull1_14 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy14 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_14.bound (by norm_num) hn lowTIParameters14_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_15 : FrameRectangleCertificate 8250 8500 (187/400) (117/250) lowTIParameters15 where
  full := (54621023031/500000000000)
  energy := (88073364143/125000000000)
  cov := (287332579981/1000000000000)
  schur := (261590141447/250000000000)
  cap := (97823049/100000000000)
  W2 := (1811878386549/500000000000)
  V := (292732603/1000000000000)
  mass := (141752633/1000000000000)
  rootN := (511458836513/500000000000)
  rootB := (15638338227/500000000000)
  rootU := (629179310153/1000000000000)
  rootV := (4277357559/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_15.scalar_checked
  centre := fun n hn => lowFull1_15 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy15 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_15.bound (by norm_num) hn lowTIParameters15_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_16 : FrameRectangleCertificate 8250 8500 (117/250) (937/2000) lowTIParameters16 where
  full := (13665909143/125000000000)
  energy := (140868341089/200000000000)
  cov := (287385477019/1000000000000)
  schur := (65351682261/62500000000)
  cap := (61158807/62500000000)
  W2 := (56570583157/15625000000)
  V := (146393247/500000000000)
  mass := (138458193/1000000000000)
  rootN := (1022559003763/1000000000000)
  rootB := (31281638577/1000000000000)
  rootU := (125828659087/200000000000)
  rootV := (133679727/7812500000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_16.scalar_checked
  centre := fun n hn => lowFull1_16 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy16 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_16.bound (by norm_num) hn lowTIParameters16_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_17 : FrameRectangleCertificate 8250 8500 (937/2000) (469/1000) lowTIParameters17 where
  full := (109412668689/1000000000000)
  energy := (704096613301/1000000000000)
  cov := (143845745139/500000000000)
  schur := (65363405903/62500000000)
  cap := (979420513/1000000000000)
  W2 := (904321293081/250000000000)
  V := (293098259/1000000000000)
  mass := (67731197/500000000000)
  rootN := (511325359837/500000000000)
  rootB := (78239237/2500000000)
  rootU := (629107959029/1000000000000)
  rootV := (3424022541/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_17.scalar_checked
  centre := fun n hn => lowFull1_17 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy17 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_17.bound (by norm_num) hn lowTIParameters17_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_18 : FrameRectangleCertificate 8250 8500 (469/1000) (939/2000) lowTIParameters18 where
  full := (10949823503/100000000000)
  energy := (703851636627/1000000000000)
  cov := (287743913413/1000000000000)
  schur := (522540902989/500000000000)
  cap := (489865297/500000000000)
  W2 := (361406029921/100000000000)
  V := (293151667/1000000000000)
  mass := (132737113/1000000000000)
  rootN := (511146213421/500000000000)
  rootB := (1565032423/50000000000)
  rootU := (629073305789/1000000000000)
  rootV := (4280418109/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_18.scalar_checked
  centre := fun n hn => lowFull1_18 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy18 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_18.bound (by norm_num) hn lowTIParameters18_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_19 : FrameRectangleCertificate 8250 8500 (939/2000) (47/100) lowTIParameters19 where
  full := (54791987259/500000000000)
  energy := (351803387671/500000000000)
  cov := (288049656973/1000000000000)
  schur := (1045269452577/1000000000000)
  cap := (980610257/1000000000000)
  W2 := (1805421339117/500000000000)
  V := (293463157/1000000000000)
  mass := (65128487/500000000000)
  rootN := (511192100041/500000000000)
  rootB := (31314697141/1000000000000)
  rootU := (125807868123/200000000000)
  rootV := (17130766387/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_19.scalar_checked
  centre := fun n hn => lowFull1_19 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy19 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_19.bound (by norm_num) hn lowTIParameters19_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_20 : FrameRectangleCertificate 8250 8500 (47/100) (941/2000) lowTIParameters20 where
  full := (109669889533/1000000000000)
  energy := (703362029363/1000000000000)
  cov := (288101606599/1000000000000)
  schur := (1044537718887/1000000000000)
  cap := (490460011/500000000000)
  W2 := (3607632284877/1000000000000)
  V := (293516083/1000000000000)
  mass := (127999069/1000000000000)
  rootN := (511013140459/500000000000)
  rootB := (31319642751/1000000000000)
  rootU := (629006068459/1000000000000)
  rootV := (8566155541/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_20.scalar_checked
  centre := fun n hn => lowFull1_20 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy20 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_20.bound (by norm_num) hn lowTIParameters20_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_21 : FrameRectangleCertificate 8250 8500 (941/2000) (471/1000) lowTIParameters21 where
  full := (109755982481/1000000000000)
  energy := (175779349653/250000000000)
  cov := (144203540409/500000000000)
  schur := (1044725432059/1000000000000)
  cap := (98179977/100000000000)
  W2 := (3604429094931/1000000000000)
  V := (146913649/500000000000)
  mass := (12594271/100000000000)
  rootN := (1022118110621/1000000000000)
  rootB := (1958355267/62500000000)
  rootU := (39310843397/62500000000)
  rootV := (2142673921/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_21.scalar_checked
  centre := fun n hn => lowFull1_21 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy21 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_21.bound (by norm_num) hn lowTIParameters21_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_22 : FrameRectangleCertificate 8250 8500 (471/1000) (943/2000) lowTIParameters22 where
  full := (109842255793/1000000000000)
  energy := (702872883003/1000000000000)
  cov := (288712555307/1000000000000)
  schur := (104491326091/100000000000)
  cap := (122834981/125000000000)
  W2 := (450154135509/125000000000)
  V := (294138513/1000000000000)
  mass := (62034603/500000000000)
  rootN := (1022209988657/1000000000000)
  rootB := (15673862383/500000000000)
  rootU := (628941623357/1000000000000)
  rootV := (3430093369/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_22.scalar_checked
  centre := fun n hn => lowFull1_22 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy22 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_22.bound (by norm_num) hn lowTIParameters22_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_23 : FrameRectangleCertificate 8250 8500 (943/2000) (59/125) lowTIParameters23 where
  full := (27482177981/250000000000)
  energy := (702628482457/1000000000000)
  cov := (289018030059/1000000000000)
  schur := (522550602527/500000000000)
  cap := (491780129/500000000000)
  W2 := (1799022114121/500000000000)
  V := (294449729/1000000000000)
  mass := (24472333/200000000000)
  rootN := (40892076593/40000000000)
  rootB := (7840441067/250000000000)
  rootU := (157227615151/250000000000)
  rootV := (17159537553/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_23.scalar_checked
  centre := fun n hn => lowFull1_23 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy23 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_23.bound (by norm_num) hn lowTIParameters23_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_24 : FrameRectangleCertificate 8250 8500 (59/125) (189/400) lowTIParameters24 where
  full := (110015353359/1000000000000)
  energy := (140476839379/200000000000)
  cov := (72330876269/250000000000)
  schur := (522644632061/500000000000)
  cap := (98444101/100000000000)
  W2 := (3594862503509/1000000000000)
  V := (58952189/200000000000)
  mass := (120804811/1000000000000)
  rootN := (1022393888931/1000000000000)
  rootB := (15687901469/500000000000)
  rootU := (628880011291/1000000000000)
  rootV := (17168603467/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_24.scalar_checked
  centre := fun n hn => lowFull1_24 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy24 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_24.bound (by norm_num) hn lowTIParameters24_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_25 : FrameRectangleCertificate 8250 8500 (189/400) (473/1000) lowTIParameters25 where
  full := (110102182603/1000000000000)
  energy := (351070013117/500000000000)
  cov := (289628980359/1000000000000)
  schur := (522738718861/500000000000)
  cap := (985322107/1000000000000)
  W2 := (1795843942959/500000000000)
  V := (295072161/1000000000000)
  mass := (119384829/1000000000000)
  rootN := (102248591077/100000000000)
  rootB := (1255593633/40000000000)
  rootU := (314425140323/500000000000)
  rootV := (17177664597/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_25.scalar_checked
  centre := fun n hn => lowFull1_25 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy25 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_25.bound (by norm_num) hn lowTIParameters25_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_26 : FrameRectangleCertificate 8250 8500 (473/1000) (947/2000) lowTIParameters26 where
  full := (110189202193/1000000000000)
  energy := (350947985197/500000000000)
  cov := (289934455907/1000000000000)
  schur := (522832862741/500000000000)
  cap := (246550889/250000000000)
  W2 := (3588520351729/1000000000000)
  V := (147691689/500000000000)
  mass := (230643/1953125000)
  rootN := (255644495037/250000000000)
  rootB := (31403878041/1000000000000)
  rootU := (628821273981/1000000000000)
  rootV := (17186720979/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_26.scalar_checked
  centre := fun n hn => lowFull1_26 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy26 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_26.bound (by norm_num) hn lowTIParameters26_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_27 : FrameRectangleCertificate 8250 8500 (947/2000) (237/500) lowTIParameters27 where
  full := (11027641469/100000000000)
  energy := (701652029291/1000000000000)
  cov := (7255998293/25000000000)
  schur := (1045854127011/1000000000000)
  cap := (987085361/1000000000000)
  W2 := (3585359877219/1000000000000)
  V := (59138919/200000000000)
  mass := (116906653/1000000000000)
  rootN := (51133504843/50000000000)
  rootB := (31417914651/1000000000000)
  rootU := (78599124581/125000000000)
  rootV := (17195772591/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_27.scalar_checked
  centre := fun n hn => lowFull1_27 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy27 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_27.bound (by norm_num) hn lowTIParameters27_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_28 : FrameRectangleCertificate 8250 8500 (237/500) (949/2000) lowTIParameters28 where
  full := (110363822683/1000000000000)
  energy := (701408202847/1000000000000)
  cov := (58109081559/200000000000)
  schur := (1046042641923/1000000000000)
  cap := (98796753/100000000000)
  W2 := (3582206438837/1000000000000)
  V := (74001453/250000000000)
  mass := (115826891/1000000000000)
  rootN := (511381130353/500000000000)
  rootB := (31431950783/1000000000000)
  rootU := (628765454069/1000000000000)
  rootV := (8602409721/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_28.scalar_checked
  centre := fun n hn => lowFull1_28 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy28 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_28.bound (by norm_num) hn lowTIParameters28_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_29 : FrameRectangleCertificate 8250 8500 (949/2000) (19/40) lowTIParameters29 where
  full := (22090285757/200000000000)
  energy := (87645561373/125000000000)
  cov := (58170176827/200000000000)
  schur := (26155781747/25000000000)
  cap := (494425033/500000000000)
  W2 := (1789530006601/500000000000)
  V := (296317029/1000000000000)
  mass := (114840643/1000000000000)
  rootN := (1022854471507/1000000000000)
  rootB := (6289197297/200000000000)
  rootU := (628738651719/1000000000000)
  rootV := (17213861537/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_29.scalar_checked
  centre := fun n hn => lowFull1_29 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy29 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_29.bound (by norm_num) hn lowTIParameters29_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_30 : FrameRectangleCertificate 8250 8500 (19/40) (951/2000) lowTIParameters30 where
  full := (110539235639/1000000000000)
  energy := (350460446809/500000000000)
  cov := (291156360739/1000000000000)
  schur := (1046420010483/1000000000000)
  cap := (494866489/500000000000)
  W2 := (44699007211/12500000000)
  V := (296628247/1000000000000)
  mass := (22787899/200000000000)
  rootN := (204589345811/200000000000)
  rootB := (31460021901/1000000000000)
  rootU := (62871259513/100000000000)
  rootV := (8611449457/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_30.scalar_checked
  centre := fun n hn => lowFull1_30 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy30 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_30.bound (by norm_num) hn lowTIParameters30_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_31 : FrameRectangleCertificate 8250 8500 (951/2000) (119/250) lowTIParameters31 where
  full := (27656811479/250000000000)
  energy := (700677410671/1000000000000)
  cov := (72865459401/250000000000)
  schur := (1046608863369/1000000000000)
  cap := (990616269/1000000000000)
  W2 := (3572788106677/1000000000000)
  V := (37117433/125000000000)
  mass := (14139477/125000000000)
  rootN := (1023039033161/1000000000000)
  rootB := (31474057079/1000000000000)
  rootU := (314343644951/500000000000)
  rootV := (17231931523/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_31.scalar_checked
  centre := fun n hn => lowFull1_31 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy31 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_31.bound (by norm_num) hn lowTIParameters31_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_32 : FrameRectangleCertificate 8250 8500 (119/250) (953/2000) lowTIParameters32 where
  full := (13839432789/125000000000)
  energy := (350217021031/500000000000)
  cov := (291767314731/1000000000000)
  schur := (523398914077/500000000000)
  cap := (198299989/200000000000)
  W2 := (892415644847/250000000000)
  V := (297250683/1000000000000)
  mass := (28090671/250000000000)
  rootN := (1023131383623/1000000000000)
  rootB := (6297618423/200000000000)
  rootU := (628662741679/1000000000000)
  rootV := (8620479729/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_32.scalar_checked
  centre := fun n hn => lowFull1_32 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy32 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_32.bound (by norm_num) hn lowTIParameters32_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_33 : FrameRectangleCertificate 8250 8500 (953/2000) (477/1000) lowTIParameters33 where
  full := (110803887551/1000000000000)
  energy := (700190787709/1000000000000)
  cov := (292072792121/1000000000000)
  schur := (523493452241/500000000000)
  cap := (992384017/1000000000000)
  W2 := (445817996497/125000000000)
  V := (297561901/1000000000000)
  mass := (55836911/500000000000)
  rootN := (1023223780257/1000000000000)
  rootB := (31502127183/1000000000000)
  rootU := (157159739043/250000000000)
  rootV := (8624991319/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_33.scalar_checked
  centre := fun n hn => lowFull1_33 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy33 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_33.bound (by norm_num) hn lowTIParameters33_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_34 : FrameRectangleCertificate 8250 8500 (477/1000) (191/400) lowTIParameters34 where
  full := (27723131097/250000000000)
  energy := (349973823769/500000000000)
  cov := (29237826977/100000000000)
  schur := (523588045991/500000000000)
  cap := (496634243/500000000000)
  W2 := (3563432261551/1000000000000)
  V := (1861707/6250000000)
  mass := (111043529/1000000000000)
  rootN := (1023316222867/1000000000000)
  rootB := (31516162299/1000000000000)
  rootU := (628615939163/1000000000000)
  rootV := (1725900113/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_34.scalar_checked
  centre := fun n hn => lowFull1_34 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy34 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_34.bound (by norm_num) hn lowTIParameters34_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_35 : FrameRectangleCertificate 8250 8500 (191/400) (239/500) lowTIParameters35 where
  full := (55490687801/500000000000)
  energy := (349852310731/500000000000)
  cov := (292683747683/1000000000000)
  schur := (1047365390301/1000000000000)
  cap := (994153359/1000000000000)
  W2 := (1780163712607/500000000000)
  V := (298184339/1000000000000)
  mass := (110466631/1000000000000)
  rootN := (1023408711269/1000000000000)
  rootB := (15765098787/500000000000)
  rootU := (78574212059/125000000000)
  rootV := (269812733/15625000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_35.scalar_checked
  centre := fun n hn => lowFull1_35 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy35 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_35.bound (by norm_num) hn lowTIParameters35_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_36 : FrameRectangleCertificate 8250 8500 (239/500) (957/2000) lowTIParameters36 where
  full := (55535222001/500000000000)
  energy := (699461709407/1000000000000)
  cov := (58597845171/200000000000)
  schur := (523777399533/500000000000)
  cap := (248759661/250000000000)
  W2 := (3557229440273/1000000000000)
  V := (149247779/500000000000)
  mass := (54969213/500000000000)
  rootN := (1023501245269/1000000000000)
  rootB := (15772116567/500000000000)
  rootU := (314286116997/500000000000)
  rootV := (2159627999/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_36.scalar_checked
  centre := fun n hn => lowFull1_36 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy36 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_36.bound (by norm_num) hn lowTIParameters36_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_37 : FrameRectangleCertificate 8250 8500 (957/2000) (479/1000) lowTIParameters37 where
  full := (111159732429/1000000000000)
  energy := (699218911291/1000000000000)
  cov := (73323676071/250000000000)
  schur := (261936079477/250000000000)
  cap := (199184869/200000000000)
  W2 := (1777069142037/500000000000)
  V := (298806777/1000000000000)
  mass := (109454643/1000000000000)
  rootN := (1023593824673/1000000000000)
  rootB := (7889567261/250000000000)
  rootU := (62855155769/100000000000)
  rootV := (2160753547/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_37.scalar_checked
  centre := fun n hn => lowFull1_37 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy37 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_37.bound (by norm_num) hn lowTIParameters37_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_38 : FrameRectangleCertificate 8250 8500 (479/1000) (959/2000) lowTIParameters38 where
  full := (22249848749/200000000000)
  energy := (349488113519/500000000000)
  cov := (4587502859/15625000000)
  schur := (261983486627/250000000000)
  cap := (996810471/1000000000000)
  W2 := (1775526967061/500000000000)
  V := (299117997/1000000000000)
  mass := (109011399/1000000000000)
  rootN := (511843224657/500000000000)
  rootB := (7893076361/250000000000)
  rootU := (628531673561/1000000000000)
  rootV := (17295028101/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_38.scalar_checked
  centre := fun n hn => lowFull1_38 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy38 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_38.bound (by norm_num) hn lowTIParameters38_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_39 : FrameRectangleCertificate 8250 8500 (959/2000) (12/25) lowTIParameters39 where
  full := (111338980849/1000000000000)
  energy := (139746731313/200000000000)
  cov := (146952830963/500000000000)
  schur := (1048123684469/1000000000000)
  cap := (249424257/250000000000)
  W2 := (3547976367919/1000000000000)
  V := (299429217/1000000000000)
  mass := (27151291/250000000000)
  rootN := (204755823797/200000000000)
  rootB := (31586342429/1000000000000)
  rootU := (628512587687/1000000000000)
  rootV := (3460804629/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_39.scalar_checked
  centre := fun n hn => lowFull1_39 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy39 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_39.bound (by norm_num) hn lowTIParameters39_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_40 : FrameRectangleCertificate 8250 8500 (12/25) (961/2000) lowTIParameters40 where
  full := (111428946663/1000000000000)
  energy := (698491199793/1000000000000)
  cov := (291637892843/1000000000000)
  schur := (1039151615459/1000000000000)
  cap := (496405391/500000000000)
  W2 := (1772452781563/500000000000)
  V := (74279707/250000000000)
  mass := (54116363/500000000000)
  rootN := (127423482889/125000000000)
  rootB := (6301780009/200000000000)
  rootU := (125698861239/200000000000)
  rootV := (3447427029/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_40.scalar_checked
  centre := fun n hn => lowFull1_40 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy40 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_40.bound (by norm_num) hn lowTIParameters40_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_41 : FrameRectangleCertificate 8250 8500 (961/2000) (481/1000) lowTIParameters41 where
  full := (6969946509/62500000000)
  energy := (698248856647/1000000000000)
  cov := (291940692943/1000000000000)
  schur := (20786798033/20000000000)
  cap := (993692707/1000000000000)
  W2 := (442730187193/125000000000)
  V := (297427319/1000000000000)
  mass := (53945581/500000000000)
  rootN := (203896042301/200000000000)
  rootB := (15761445897/500000000000)
  rootU := (628476835293/1000000000000)
  rootV := (8623040633/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_41.scalar_checked
  centre := fun n hn => lowFull1_41 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy41 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_41.bound (by norm_num) hn lowTIParameters41_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_42 : FrameRectangleCertificate 8250 8500 (481/1000) (963/2000) lowTIParameters42 where
  full := (55804788137/500000000000)
  energy := (349003313523/500000000000)
  cov := (292243493301/1000000000000)
  schur := (41581131809/40000000000)
  cap := (497287541/500000000000)
  W2 := (70775682981/20000000000)
  V := (29773581/100000000000)
  mass := (26894453/250000000000)
  rootN := (254893151049/250000000000)
  rootB := (31536884469/1000000000000)
  rootU := (314230090619/500000000000)
  rootV := (4313755687/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_42.scalar_checked
  centre := fun n hn => lowFull1_42 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy42 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_42.bound (by norm_num) hn lowTIParameters42_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_43 : FrameRectangleCertificate 8250 8500 (963/2000) (241/500) lowTIParameters43 where
  full := (111700246067/1000000000000)
  energy := (697764510909/1000000000000)
  cov := (292546293909/1000000000000)
  schur := (51985839789/50000000000)
  cap := (248864479/250000000000)
  W2 := (441966686939/125000000000)
  V := (149022151/500000000000)
  mass := (53645127/500000000000)
  rootN := (254916260243/250000000000)
  rootB := (31550878213/1000000000000)
  rootU := (314222175171/500000000000)
  rootV := (17263959627/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_43.scalar_checked
  centre := fun n hn => lowFull1_43 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy43 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_43.bound (by norm_num) hn lowTIParameters43_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_44 : FrameRectangleCertificate 8250 8500 (241/500) (193/400) lowTIParameters44 where
  full := (55895578283/500000000000)
  energy := (348761254081/500000000000)
  cov := (292849094777/1000000000000)
  schur := (519952701521/500000000000)
  cap := (996341213/1000000000000)
  W2 := (706537903017/200000000000)
  V := (298352793/1000000000000)
  mass := (107026281/1000000000000)
  rootN := (101975752169/100000000000)
  rootB := (246600571/7812500000)
  rootU := (628429348997/1000000000000)
  rootV := (3454578371/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_44.scalar_checked
  centre := fun n hn => lowFull1_44 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy44 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_44.bound (by norm_num) hn lowTIParameters44_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_45 : FrameRectangleCertificate 8250 8500 (193/400) (483/1000) lowTIParameters45 where
  full := (22376462169/200000000000)
  energy := (174320154681/250000000000)
  cov := (36643986987/125000000000)
  schur := (520047058309/500000000000)
  cap := (997224983/1000000000000)
  W2 := (3529652185869/1000000000000)
  V := (59732257/200000000000)
  mass := (106783883/1000000000000)
  rootN := (15935156971/15625000000)
  rootB := (31578869249/1000000000000)
  rootU := (157103795911/250000000000)
  rootV := (8640909747/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_45.scalar_checked
  centre := fun n hn => lowFull1_45 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy45 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_45.bound (by norm_num) hn lowTIParameters45_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_46 : FrameRectangleCertificate 8250 8500 (483/1000) (967/2000) lowTIParameters46 where
  full := (111973712007/1000000000000)
  energy := (348519421259/500000000000)
  cov := (29345469727/100000000000)
  schur := (1040282936191/1000000000000)
  cap := (998109229/1000000000000)
  W2 := (1763310743073/500000000000)
  V := (298969777/1000000000000)
  mass := (53280613/500000000000)
  rootN := (509971307083/500000000000)
  rootB := (31592866743/1000000000000)
  rootU := (628401860793/1000000000000)
  rootV := (4322685631/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_46.scalar_checked
  centre := fun n hn => lowFull1_46 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy46 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_46.bound (by norm_num) hn lowTIParameters46_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_47 : FrameRectangleCertificate 8250 8500 (967/2000) (121/250) lowTIParameters47 where
  full := (112065363187/1000000000000)
  energy := (87099647433/125000000000)
  cov := (58751499779/200000000000)
  schur := (520235930697/500000000000)
  cap := (24974849/25000000000)
  W2 := (704719478837/200000000000)
  V := (29927827/100000000000)
  mass := (106356639/1000000000000)
  rootN := (510017612783/500000000000)
  rootB := (3160686571/100000000000)
  rootU := (2454646043/3906250000)
  rootV := (864983049/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_47.scalar_checked
  centre := fun n hn => lowFull1_47 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy47 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_47.bound (by norm_num) hn lowTIParameters47_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_48 : FrameRectangleCertificate 8250 8500 (121/250) (969/2000) lowTIParameters48 where
  full := (112157267551/1000000000000)
  energy := (348277814743/500000000000)
  cov := (147030150387/500000000000)
  schur := (1040660891911/1000000000000)
  cap := (999879183/1000000000000)
  W2 := (3520579888497/1000000000000)
  V := (149793381/500000000000)
  mass := (106168597/1000000000000)
  rootN := (63757992511/62500000000)
  rootB := (1581043313/50000000000)
  rootU := (628377768933/1000000000000)
  rootV := (4327143703/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_48.scalar_checked
  centre := fun n hn => lowFull1_48 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy48 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_48.bound (by norm_num) hn lowTIParameters48_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_49 : FrameRectangleCertificate 8250 8500 (969/2000) (97/200) lowTIParameters49 where
  full := (56124714147/500000000000)
  energy := (348157096253/500000000000)
  cov := (147181551453/500000000000)
  schur := (1040850027411/1000000000000)
  cap := (1000764907/1000000000000)
  W2 := (3517568947601/1000000000000)
  V := (59979051/200000000000)
  mass := (105995711/1000000000000)
  rootN := (510110288911/500000000000)
  rootB := (7908717133/250000000000)
  rootU := (31418350663/50000000000)
  rootV := (3463496817/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_49.scalar_checked
  centre := fun n hn => lowFull1_49 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy49 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_49.bound (by norm_num) hn lowTIParameters49_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_50 : FrameRectangleCertificate 8250 8500 (97/200) (971/2000) lowTIParameters50 where
  full := (22468369729/200000000000)
  energy := (139214573689/200000000000)
  cov := (36833238161/125000000000)
  schur := (520519633767/500000000000)
  cap := (200330227/200000000000)
  W2 := (351456455009/100000000000)
  V := (75050937/250000000000)
  mass := (105836709/1000000000000)
  rootN := (1020313318317/1000000000000)
  rootB := (31648872571/1000000000000)
  rootU := (19636160211/31250000000)
  rootV := (2165798597/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_50.scalar_checked
  centre := fun n hn => lowFull1_50 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy50 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_50.bound (by norm_num) hn lowTIParameters50_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_51 : FrameRectangleCertificate 8250 8500 (971/2000) (243/500) lowTIParameters51 where
  full := (14054316483/125000000000)
  energy := (695831657229/1000000000000)
  cov := (147484353961/500000000000)
  schur := (1041228611973/1000000000000)
  cap := (1002537877/1000000000000)
  W2 := (3511566674731/1000000000000)
  V := (150256121/500000000000)
  mass := (1651413/15625000000)
  rootN := (510203050749/500000000000)
  rootB := (15831439267/500000000000)
  rootU := (628348116241/1000000000000)
  rootV := (8667644461/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_51.scalar_checked
  centre := fun n hn => lowFull1_51 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy51 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_51.bound (by norm_num) hn lowTIParameters51_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_52 : FrameRectangleCertificate 8250 8500 (243/500) (973/2000) lowTIParameters52 where
  full := (2813187031/25000000000)
  energy := (86948819847/125000000000)
  cov := (36908938851/125000000000)
  schur := (520709030189/500000000000)
  cap := (1003425139/1000000000000)
  W2 := (87714382507/25000000000)
  V := (60164147/200000000000)
  mass := (105555823/1000000000000)
  rootN := (510249463591/500000000000)
  rootB := (31676886511/1000000000000)
  rootU := (314169994303/500000000000)
  rootV := (17344184473/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_52.scalar_checked
  centre := fun n hn => lowFull1_52 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy52 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_52.bound (by norm_num) hn lowTIParameters52_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_53 : FrameRectangleCertificate 8250 8500 (973/2000) (487/1000) lowTIParameters53 where
  full := (22524140019/200000000000)
  energy := (69534957301/100000000000)
  cov := (36946789243/125000000000)
  schur := (1041607612427/1000000000000)
  cap := (100431293/100000000000)
  W2 := (1752795202833/500000000000)
  V := (301129229/1000000000000)
  mass := (13178989/125000000000)
  rootN := (1020591795199/1000000000000)
  rootB := (31690896643/1000000000000)
  rootU := (157083187701/250000000000)
  rootV := (4338268873/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_53.scalar_checked
  centre := fun n hn => lowFull1_53 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy53 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_53.bound (by norm_num) hn lowTIParameters53_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_54 : FrameRectangleCertificate 8250 8500 (487/1000) (39/80) lowTIParameters54 where
  full := (56357095893/500000000000)
  energy := (43444293741/62500000000)
  cov := (295877117331/1000000000000)
  schur := (1041797267793/1000000000000)
  cap := (502600629/500000000000)
  W2 := (3502611969909/1000000000000)
  V := (301437723/1000000000000)
  mass := (105317817/1000000000000)
  rootN := (1020684705379/1000000000000)
  rootB := (31704909053/1000000000000)
  rootU := (628326409861/1000000000000)
  rootV := (8680980979/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_54.scalar_checked
  centre := fun n hn => lowFull1_54 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy54 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_54.bound (by norm_num) hn lowTIParameters54_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_55 : FrameRectangleCertificate 8250 8500 (39/80) (61/125) lowTIParameters55 where
  full := (112807959699/1000000000000)
  energy := (694867939233/1000000000000)
  cov := (296179920967/1000000000000)
  schur := (1041987026139/1000000000000)
  cap := (1006090127/1000000000000)
  W2 := (3499639972037/1000000000000)
  V := (150873109/500000000000)
  mass := (105212729/1000000000000)
  rootN := (127597207193/125000000000)
  rootB := (158594619/5000000000)
  rootU := (628320972853/1000000000000)
  rootV := (8685421953/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_55.scalar_checked
  centre := fun n hn => lowFull1_55 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy55 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_55.bound (by norm_num) hn lowTIParameters55_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_56 : FrameRectangleCertificate 8250 8500 (61/125) (977/2000) lowTIParameters56 where
  full := (112902007253/1000000000000)
  energy := (173656822767/250000000000)
  cov := (296482724853/1000000000000)
  schur := (208435377429/200000000000)
  cap := (251744887/250000000000)
  W2 := (437084298909/125000000000)
  V := (37756839/125000000000)
  mass := (26278977/250000000000)
  rootN := (40834826061/40000000000)
  rootB := (6346588211/200000000000)
  rootU := (157079111733/250000000000)
  rootV := (17379721287/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_56.scalar_checked
  centre := fun n hn => lowFull1_56 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy56 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_56.bound (by norm_num) hn lowTIParameters56_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_57 : FrameRectangleCertificate 8250 8500 (977/2000) (489/1000) lowTIParameters57 where
  full := (112996337899/1000000000000)
  energy := (8679834441/12500000000)
  cov := (148392764493/500000000000)
  schur := (1042366850481/1000000000000)
  cap := (1007869527/1000000000000)
  W2 := (3493715206861/1000000000000)
  V := (302363207/1000000000000)
  mass := (105026679/1000000000000)
  rootN := (63810230447/62500000000)
  rootB := (3174696091/100000000000)
  rootU := (628312839307/1000000000000)
  rootV := (4347148541/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_57.scalar_checked
  centre := fun n hn => lowFull1_57 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy57 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_57.bound (by norm_num) hn lowTIParameters57_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_58 : FrameRectangleCertificate 8250 8500 (489/1000) (979/2000) lowTIParameters58 where
  full := (56545477563/500000000000)
  energy := (694146331799/1000000000000)
  cov := (297088333367/1000000000000)
  schur := (1042556915841/1000000000000)
  cap := (1008760071/1000000000000)
  W2 := (3490762398223/1000000000000)
  V := (302671703/1000000000000)
  mass := (52472211/500000000000)
  rootN := (51052838213/50000000000)
  rootB := (31760983471/1000000000000)
  rootU := (314155078637/500000000000)
  rootV := (3479492509/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_58.scalar_checked
  centre := fun n hn => lowFull1_58 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy58 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_58.bound (by norm_num) hn lowTIParameters58_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_59 : FrameRectangleCertificate 8250 8500 (979/2000) (49/100) lowTIParameters59 where
  full := (7074116403/62500000000)
  energy := (346953010271/500000000000)
  cov := (148695568999/500000000000)
  schur := (521373541453/500000000000)
  cap := (100965119/100000000000)
  W2 := (435976993093/125000000000)
  V := (151490099/500000000000)
  mass := (10486857/100000000000)
  rootN := (204229976537/200000000000)
  rootB := (31775008891/1000000000000)
  rootU := (628308408161/1000000000000)
  rootV := (17406326379/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_59.scalar_checked
  centre := fun n hn => lowFull1_59 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy59 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_59.bound (by norm_num) hn lowTIParameters59_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_60 : FrameRectangleCertificate 8250 8500 (49/100) (981/2000) lowTIParameters60 where
  full := (56640531709/500000000000)
  energy := (173416455359/250000000000)
  cov := (295100967529/1000000000000)
  schur := (1033860415121/1000000000000)
  cap := (502366077/500000000000)
  W2 := (3484875825957/1000000000000)
  V := (300646987/1000000000000)
  mass := (52399303/500000000000)
  rootN := (254197316951/250000000000)
  rootB := (15848755109/500000000000)
  rootU := (125661519877/200000000000)
  rootV := (17339174923/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_60.scalar_checked
  centre := fun n hn => lowFull1_60 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy60 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_60.bound (by norm_num) hn lowTIParameters60_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_61 : FrameRectangleCertificate 8250 8500 (981/2000) (491/1000) lowTIParameters61 where
  full := (113376561621/1000000000000)
  energy := (346712867201/500000000000)
  cov := (14770056389/50000000000)
  schur := (1034049118529/1000000000000)
  cap := (1005619017/1000000000000)
  W2 := (3481942021503/1000000000000)
  V := (75238197/250000000000)
  mass := (20946811/200000000000)
  rootN := (203376411467/200000000000)
  rootB := (31711496607/1000000000000)
  rootU := (628307738423/1000000000000)
  rootV := (17347990893/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_61.scalar_checked
  centre := fun n hn => lowFull1_61 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy61 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_61.bound (by norm_num) hn lowTIParameters61_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_62 : FrameRectangleCertificate 8250 8500 (491/1000) (983/2000) lowTIParameters62 where
  full := (56736180339/500000000000)
  energy := (693185759367/1000000000000)
  cov := (11828051531/40000000000)
  schur := (103423792181/100000000000)
  cap := (1006506479/1000000000000)
  W2 := (3479014511131/1000000000000)
  V := (30125859/100000000000)
  mass := (104674479/1000000000000)
  rootN := (1016974887503/1000000000000)
  rootB := (31725486269/1000000000000)
  rootU := (62830883283/100000000000)
  rootV := (17356802413/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_62.scalar_checked
  centre := fun n hn => lowFull1_62 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy62 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_62.bound (by norm_num) hn lowTIParameters62_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_63 : FrameRectangleCertificate 8250 8500 (983/2000) (123/250) lowTIParameters63 where
  full := (113568464239/1000000000000)
  energy := (346472948127/500000000000)
  cov := (37000181127/125000000000)
  schur := (1034426824643/1000000000000)
  cap := (1007394549/1000000000000)
  W2 := (695218654919/200000000000)
  V := (37695549/125000000000)
  mass := (52309741/500000000000)
  rootN := (508533879069/500000000000)
  rootB := (1983717459/62500000000)
  rootU := (628310890203/1000000000000)
  rootV := (17365609463/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_63.scalar_checked
  centre := fun n hn => lowFull1_63 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy63 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_63.bound (by norm_num) hn lowTIParameters63_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_64 : FrameRectangleCertificate 8250 8500 (123/250) (197/400) lowTIParameters64 where
  full := (14208109499/125000000000)
  energy := (346353072493/500000000000)
  cov := (296301609999/1000000000000)
  schur := (258653956679/250000000000)
  cap := (1008283231/1000000000000)
  W2 := (3473178291797/1000000000000)
  V := (150935097/500000000000)
  mass := (13071087/125000000000)
  rootN := (1017160669077/1000000000000)
  rootB := (31753475889/1000000000000)
  rootU := (25132556729/40000000000)
  rootV := (1085900753/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_64.scalar_checked
  centre := fun n hn => lowFull1_64 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy64 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_64.bound (by norm_num) hn lowTIParameters64_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_65 : FrameRectangleCertificate 8250 8500 (197/400) (493/1000) lowTIParameters65 where
  full := (113761599659/1000000000000)
  energy := (346233252743/500000000000)
  cov := (148300885613/500000000000)
  schur := (32337653991/31250000000)
  cap := (1009172537/1000000000000)
  W2 := (86756738567/25000000000)
  V := (75543999/250000000000)
  mass := (104521787/1000000000000)
  rootN := (127156702519/125000000000)
  rootB := (3970934511/125000000000)
  rootU := (3926987029/6250000000)
  rootV := (271612659/15625000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_65.scalar_checked
  centre := fun n hn => lowFull1_65 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy65 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_65.bound (by norm_num) hn lowTIParameters65_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_66 : FrameRectangleCertificate 8250 8500 (493/1000) (987/2000) lowTIParameters66 where
  full := (28464659749/250000000000)
  energy := (8652837221/12500000000)
  cov := (59380386539/200000000000)
  schur := (129374265917/125000000000)
  cap := (252515619/250000000000)
  W2 := (1733683503669/500000000000)
  V := (302481799/1000000000000)
  mass := (104478447/1000000000000)
  rootN := (127168326401/125000000000)
  rootB := (31781480079/1000000000000)
  rootU := (628322917261/1000000000000)
  rootV := (8696001941/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_66.scalar_checked
  centre := fun n hn => lowFull1_66 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy66 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_66.bound (by norm_num) hn lowTIParameters66_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_67 : FrameRectangleCertificate 8250 8500 (987/2000) (247/500) lowTIParameters67 where
  full := (113955997793/1000000000000)
  energy := (691987561493/1000000000000)
  cov := (74300523601/250000000000)
  schur := (1035183425263/1000000000000)
  cap := (505476527/500000000000)
  W2 := (216529416619/62500000000)
  V := (151393801/500000000000)
  mass := (104438393/1000000000000)
  rootN := (508719821037/500000000000)
  rootB := (31795487951/1000000000000)
  rootU := (125665780793/200000000000)
  rootV := (17400793143/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_67.scalar_checked
  centre := fun n hn => lowFull1_67 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy67 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_67.bound (by norm_num) hn lowTIParameters67_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_68 : FrameRectangleCertificate 8250 8500 (247/500) (989/2000) lowTIParameters68 where
  full := (114053679877/1000000000000)
  energy := (691748256849/1000000000000)
  cov := (148751128179/500000000000)
  schur := (1035372821223/1000000000000)
  cap := (1011844279/1000000000000)
  W2 := (43269756233/12500000000)
  V := (60618681/200000000000)
  mass := (104401367/1000000000000)
  rootN := (508766356303/500000000000)
  rootB := (1988093739/62500000000)
  rootU := (125667178541/200000000000)
  rootV := (1088098623/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_68.scalar_checked
  centre := fun n hn => lowFull1_68 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy68 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_68.bound (by norm_num) hn lowTIParameters68_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_69 : FrameRectangleCertificate 8250 8500 (989/2000) (99/200) lowTIParameters69 where
  full := (28537922277/250000000000)
  energy := (691509063673/1000000000000)
  cov := (37225302319/125000000000)
  schur := (64722644681/62500000000)
  cap := (6329601/6250000000)
  W2 := (864674121457/250000000000)
  V := (37924901/125000000000)
  mass := (10436713/100000000000)
  rootN := (1017625822637/1000000000000)
  rootB := (15911757917/500000000000)
  rootU := (19635746609/31250000000)
  rootV := (8709179181/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_69.scalar_checked
  centre := fun n hn => lowFull1_69 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy69 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_69.bound (by norm_num) hn lowTIParameters69_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_70 : FrameRectangleCertificate 8250 8500 (99/200) (991/2000) lowTIParameters70 where
  full := (114250029383/1000000000000)
  energy := (691269981889/1000000000000)
  cov := (149051290493/500000000000)
  schur := (258937976491/250000000000)
  cap := (1013628709/1000000000000)
  W2 := (691163721571/200000000000)
  V := (75926253/250000000000)
  mass := (104335463/1000000000000)
  rootN := (508859485999/500000000000)
  rootB := (6367507233/200000000000)
  rootU := (628352908397/1000000000000)
  rootV := (435678359/25000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_70.scalar_checked
  centre := fun n hn => lowFull1_70 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy70 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_70.bound (by norm_num) hn lowTIParameters70_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_71 : FrameRectangleCertificate 8250 8500 (991/2000) (62/125) lowTIParameters71 where
  full := (28587176159/250000000000)
  energy := (345515505711/500000000000)
  cov := (298402743661/1000000000000)
  schur := (517970797079/500000000000)
  cap := (101452193/100000000000)
  W2 := (13811787381/4000000000)
  V := (60802163/200000000000)
  mass := (104306167/1000000000000)
  rootN := (254453040137/250000000000)
  rootB := (31851560873/1000000000000)
  rootU := (628362951591/1000000000000)
  rootV := (17435905913/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_71.scalar_checked
  centre := fun n hn => lowFull1_71 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy71 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_71.bound (by norm_num) hn lowTIParameters71_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_72 : FrameRectangleCertificate 8250 8500 (62/125) (993/2000) lowTIParameters72 where
  full := (22889543767/200000000000)
  energy := (345396076099/500000000000)
  cov := (18668931661/62500000000)
  schur := (207226275831/200000000000)
  cap := (507707917/500000000000)
  W2 := (690016235709/200000000000)
  V := (304316619/1000000000000)
  mass := (6517441/62500000000)
  rootN := (254476347029/250000000000)
  rootB := (254924721/8000000000)
  rootU := (314187014643/500000000000)
  rootV := (4361168271/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_72.scalar_checked
  centre := fun n hn => lowFull1_72 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy72 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_72.bound (by norm_num) hn lowTIParameters72_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_73 : FrameRectangleCertificate 8250 8500 (993/2000) (497/1000) lowTIParameters73 where
  full := (22909415197/200000000000)
  energy := (690553404141/1000000000000)
  cov := (299003069729/1000000000000)
  schur := (518160630333/500000000000)
  cap := (1016310431/1000000000000)
  W2 := (3447221588393/1000000000000)
  V := (38077803/125000000000)
  mass := (104253961/1000000000000)
  rootN := (1017998654551/1000000000000)
  rootB := (31879624073/1000000000000)
  rootU := (628386149771/1000000000000)
  rootV := (436335897/25000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_73.scalar_checked
  centre := fun n hn => lowFull1_73 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy73 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_73.bound (by norm_num) hn lowTIParameters73_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_74 : FrameRectangleCertificate 8250 8500 (497/1000) (199/400) lowTIParameters74 where
  full := (28661695031/250000000000)
  energy := (690314767177/1000000000000)
  cov := (74825808281/250000000000)
  schur := (518255619201/500000000000)
  cap := (31787679/31250000000)
  W2 := (3444368055529/1000000000000)
  V := (76232057/250000000000)
  mass := (52115363/500000000000)
  rootN := (1018091959699/1000000000000)
  rootB := (31893662819/1000000000000)
  rootU := (314199660697/500000000000)
  rootV := (69848777/4000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_74.scalar_checked
  centre := fun n hn => lowFull1_74 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy74 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_74.bound (by norm_num) hn lowTIParameters74_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_75 : FrameRectangleCertificate 8250 8500 (199/400) (249/500) lowTIParameters75 where
  full := (28686708833/250000000000)
  energy := (690076241231/1000000000000)
  cov := (149801698377/500000000000)
  schur := (207340262411/200000000000)
  cap := (509050867/500000000000)
  W2 := (3441520560769/1000000000000)
  V := (305234033/1000000000000)
  mass := (13026151/125000000000)
  rootN := (509092651699/500000000000)
  rootB := (31907706499/1000000000000)
  rootU := (62841355259/100000000000)
  rootV := (8735474129/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_75.scalar_checked
  centre := fun n hn => lowFull1_75 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy75 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_75.bound (by norm_num) hn lowTIParameters75_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_76 : FrameRectangleCertificate 8250 8500 (249/500) (997/2000) lowTIParameters76 where
  full := (114847245723/1000000000000)
  energy := (172459456557/250000000000)
  cov := (299903560623/1000000000000)
  schur := (518445740667/500000000000)
  cap := (50949923/50000000000)
  W2 := (343867908499/100000000000)
  V := (152769919/500000000000)
  mass := (52094637/500000000000)
  rootN := (127284835687/125000000000)
  rootB := (15960877639/500000000000)
  rootU := (12568577037/20000000000)
  rootV := (17479697881/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_76.scalar_checked
  centre := fun n hn => lowFull1_76 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy76 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_76.bound (by norm_num) hn lowTIParameters76_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_77 : FrameRectangleCertificate 8250 8500 (997/2000) (499/1000) lowTIParameters77 where
  full := (114948015447/1000000000000)
  energy := (344799761047/500000000000)
  cov := (30020372473/100000000000)
  schur := (518540872979/500000000000)
  cap := (1019895913/1000000000000)
  W2 := (858960902297/250000000000)
  V := (305845643/1000000000000)
  mass := (26042701/250000000000)
  rootN := (1018372105843/1000000000000)
  rootB := (31935809259/1000000000000)
  rootU := (125689045547/200000000000)
  rootV := (17488443127/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_77.scalar_checked
  centre := fun n hn => lowFull1_77 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy77 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_77.bound (by norm_num) hn lowTIParameters77_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_78 : FrameRectangleCertificate 8250 8500 (499/1000) (999/2000) lowTIParameters78 where
  full := (57524574347/500000000000)
  energy := (344680664379/500000000000)
  cov := (18781493067/62500000000)
  schur := (1037272105639/1000000000000)
  cap := (510397051/500000000000)
  W2 := (1716507057229/500000000000)
  V := (306151449/1000000000000)
  mass := (20830737/200000000000)
  rootN := (7956762221/7812500000)
  rootB := (998433393/31250000000)
  rootU := (628462688887/1000000000000)
  rootV := (17497184031/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_78.scalar_checked
  centre := fun n hn => lowFull1_78 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy78 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_78.bound (by norm_num) hn lowTIParameters78_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_79 : FrameRectangleCertificate 8250 8500 (999/2000) (1/2) lowTIParameters79 where
  full := (14393831211/125000000000)
  energy := (689123246139/1000000000000)
  cov := (150402026827/500000000000)
  schur := (518731280041/500000000000)
  cap := (1021693039/1000000000000)
  W2 := (1715095290929/500000000000)
  V := (61291451/200000000000)
  mass := (20827563/200000000000)
  rootN := (40742362427/40000000000)
  rootB := (3196393341/100000000000)
  rootU := (157120310999/250000000000)
  rootV := (1750592057/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_79.scalar_checked
  centre := fun n hn => lowFull1_79 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy79 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_79.bound (by norm_num) hn lowTIParameters79_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_80 : FrameRectangleCertificate 8250 8500 (1/2) (1001/2000) lowTIParameters80 where
  full := (57626261347/500000000000)
  energy := (688885274171/1000000000000)
  cov := (59698358497/200000000000)
  schur := (1028657867967/1000000000000)
  cap := (508372591/500000000000)
  W2 := (3427372992681/1000000000000)
  V := (152050769/500000000000)
  mass := (104123099/1000000000000)
  rootN := (126778464997/125000000000)
  rootB := (15943220989/500000000000)
  rootU := (125700180369/200000000000)
  rootV := (17438507333/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_80.scalar_checked
  centre := fun n hn => lowFull1_80 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy80 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_80.bound (by norm_num) hn lowTIParameters80_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_81 : FrameRectangleCertificate 8250 8500 (1001/2000) (501/1000) lowTIParameters81 where
  full := (57677386007/500000000000)
  energy := (68864741277/100000000000)
  cov := (149394673029/500000000000)
  schur := (514423424611/500000000000)
  cap := (508820149/500000000000)
  W2 := (3424561328101/1000000000000)
  V := (304404683/1000000000000)
  mass := (2082189/20000000000)
  rootN := (507160440399/500000000000)
  rootB := (31900474887/1000000000000)
  rootU := (628521671267/1000000000000)
  rootV := (4361799249/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_81.scalar_checked
  centre := fun n hn => lowFull1_81 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy81 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_81.bound (by norm_num) hn lowTIParameters81_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_82 : FrameRectangleCertificate 8250 8500 (501/1000) (1003/2000) lowTIParameters82 where
  full := (57728700993/500000000000)
  energy := (688409661873/1000000000000)
  cov := (37385862483/125000000000)
  schur := (1029035923587/1000000000000)
  cap := (1018536189/1000000000000)
  W2 := (1710877784833/500000000000)
  V := (304707829/1000000000000)
  mass := (104096787/1000000000000)
  rootN := (507207039479/500000000000)
  rootB := (3989314221/125000000000)
  rootU := (19641986287/31250000000)
  rootV := (17455882361/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_82.scalar_checked
  centre := fun n hn => lowFull1_82 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy82 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_82.bound (by norm_num) hn lowTIParameters82_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_83 : FrameRectangleCertificate 8250 8500 (1003/2000) (251/500) lowTIParameters83 where
  full := (115560416989/1000000000000)
  energy := (3440860107/5000000000)
  cov := (149692226951/500000000000)
  schur := (1029225090741/1000000000000)
  cap := (31857277/31250000000)
  W2 := (6677647849/1953125000)
  V := (12200439/40000000000)
  mass := (26021259/250000000000)
  rootN := (1014507314287/1000000000000)
  rootB := (31928558753/1000000000000)
  rootU := (628566580569/1000000000000)
  rootV := (1091535213/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_83.scalar_checked
  centre := fun n hn => lowFull1_83 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy83 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_83.bound (by norm_num) hn lowTIParameters83_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_84 : FrameRectangleCertificate 8250 8500 (251/500) (201/400) lowTIParameters84 where
  full := (28915955359/250000000000)
  energy := (687934491279/1000000000000)
  cov := (149841004087/500000000000)
  schur := (257353587607/250000000000)
  cap := (204066067/200000000000)
  W2 := (3416161696769/1000000000000)
  V := (152657061/500000000000)
  mass := (104074129/1000000000000)
  rootN := (1014600586649/1000000000000)
  rootB := (15971305011/500000000000)
  rootU := (78573842309/125000000000)
  rootV := (17473240169/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_84.scalar_checked
  centre := fun n hn => lowFull1_84 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy84 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_84.bound (by norm_num) hn lowTIParameters84_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_85 : FrameRectangleCertificate 8250 8500 (201/400) (503/1000) lowTIParameters85 where
  full := (115767619787/1000000000000)
  energy := (171924267859/250000000000)
  cov := (299979562677/1000000000000)
  schur := (102960370237/100000000000)
  cap := (255307153/250000000000)
  W2 := (1706686772757/500000000000)
  V := (305617269/1000000000000)
  mass := (52032001/500000000000)
  rootN := (1014693895897/1000000000000)
  rootB := (7989166931/250000000000)
  rootU := (628616044027/1000000000000)
  rootV := (139855301/8000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_85.scalar_checked
  centre := fun n hn => lowFull1_85 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy85 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_85.bound (by norm_num) hn lowTIParameters85_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_86 : FrameRectangleCertificate 8250 8500 (503/1000) (1007/2000) lowTIParameters86 where
  full := (57935908267/500000000000)
  energy := (3437298809/5000000000)
  cov := (30027711741/100000000000)
  schur := (1029793146279/1000000000000)
  cap := (1022127703/1000000000000)
  W2 := (3410591226601/1000000000000)
  V := (61184083/200000000000)
  mass := (52027299/500000000000)
  rootN := (1014787241879/1000000000000)
  rootB := (1278829279/40000000000)
  rootU := (628642506423/1000000000000)
  rootV := (17490580751/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_86.scalar_checked
  centre := fun n hn => lowFull1_86 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy86 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_86.bound (by norm_num) hn lowTIParameters86_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_87 : FrameRectangleCertificate 8250 8500 (1007/2000) (63/125) lowTIParameters87 where
  full := (11597641621/100000000000)
  energy := (137444512459/200000000000)
  cov := (2404597379/8000000000)
  schur := (102998268189/100000000000)
  cap := (51151381/50000000000)
  W2 := (681562944357/200000000000)
  V := (153111781/500000000000)
  mass := (104045863/1000000000000)
  rootN := (1014880624453/1000000000000)
  rootB := (15992401477/500000000000)
  rootU := (15716753373/25000000000)
  rootV := (17499244613/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_87.scalar_checked
  centre := fun n hn => lowFull1_87 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy87 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_87.bound (by norm_num) hn lowTIParameters87_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_88 : FrameRectangleCertificate 8250 8500 (63/125) (1009/2000) lowTIParameters88 where
  full := (29020355847/250000000000)
  energy := (686985472849/1000000000000)
  cov := (300872227571/1000000000000)
  schur := (515086154461/500000000000)
  cap := (255982093/250000000000)
  W2 := (106407625403/31250000000)
  V := (30652671/100000000000)
  mass := (26009437/250000000000)
  rootN := (1014974043473/1000000000000)
  rootB := (31998880793/1000000000000)
  rootU := (314349469427/500000000000)
  rootV := (3501580843/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_88.scalar_checked
  centre := fun n hn => lowFull1_88 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy88 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_88.bound (by norm_num) hn lowTIParameters88_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_89 : FrameRectangleCertificate 8250 8500 (1009/2000) (101/200) lowTIParameters89 where
  full := (58093421339/500000000000)
  energy := (686748493389/1000000000000)
  cov := (60233956599/200000000000)
  schur := (1030362027099/1000000000000)
  cap := (64051873/62500000000)
  W2 := (3402279081897/1000000000000)
  V := (306829857/1000000000000)
  mass := (52015103/500000000000)
  rootN := (101506749879/100000000000)
  rootB := (4001620703/125000000000)
  rootU := (157182231907/250000000000)
  rootV := (17516559509/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_89.scalar_checked
  centre := fun n hn => lowFull1_89 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy89 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_89.bound (by norm_num) hn lowTIParameters89_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_90 : FrameRectangleCertificate 8250 8500 (101/200) (1011/2000) lowTIParameters90 where
  full := (58146339367/500000000000)
  energy := (343255811921/500000000000)
  cov := (75366834663/250000000000)
  schur := (128818979521/125000000000)
  cap := (51286621/50000000000)
  W2 := (3399519910733/1000000000000)
  V := (61426601/200000000000)
  mass := (26005799/250000000000)
  rootN := (15861890473/15625000000)
  rootB := (4003382203/125000000000)
  rootU := (628760110717/1000000000000)
  rootV := (4381302639/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_90.scalar_checked
  centre := fun n hn => lowFull1_90 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy90 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_90.bound (by norm_num) hn lowTIParameters90_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_91 : FrameRectangleCertificate 8250 8500 (1011/2000) (253/500) lowTIParameters91 where
  full := (116398936251/1000000000000)
  energy := (137254972827/200000000000)
  cov := (60352978907/200000000000)
  schur := (1030741735827/1000000000000)
  cap := (513317869/500000000000)
  W2 := (135870659259/40000000000)
  V := (307436153/1000000000000)
  mass := (52008339/500000000000)
  rootN := (507627258879/500000000000)
  rootB := (1602057847/50000000000)
  rootU := (628792497679/1000000000000)
  rootV := (8766928667/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_91.scalar_checked
  centre := fun n hn => lowFull1_91 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy91 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_91.bound (by norm_num) hn lowTIParameters91_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_92 : FrameRectangleCertificate 8250 8500 (253/500) (1013/2000) lowTIParameters92 where
  full := (29126404989/250000000000)
  energy := (343019107099/500000000000)
  cov := (151031225323/500000000000)
  schur := (1030931725841/1000000000000)
  cap := (1027539933/1000000000000)
  W2 := (3394018776331/1000000000000)
  V := (153869651/500000000000)
  mass := (104010617/1000000000000)
  rootN := (253837020281/250000000000)
  rootB := (16027631867/500000000000)
  rootU := (314413049061/500000000000)
  rootV := (17542499879/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_92.scalar_checked
  centre := fun n hn => lowFull1_92 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy92 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_92.bound (by norm_num) hn lowTIParameters92_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_93 : FrameRectangleCertificate 8250 8500 (1013/2000) (507/1000) lowTIParameters93 where
  full := (932901877/8000000000)
  energy := (685801673953/1000000000000)
  cov := (75590001747/250000000000)
  schur := (515560902959/500000000000)
  cap := (514222507/500000000000)
  W2 := (3391276777407/1000000000000)
  V := (6160849/20000000000)
  mass := (104004979/1000000000000)
  rootN := (126930210027/125000000000)
  rootB := (4008672267/125000000000)
  rootU := (314430460867/500000000000)
  rootV := (877556907/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_93.scalar_checked
  centre := fun n hn => lowFull1_93 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy93 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_93.bound (by norm_num) hn lowTIParameters93_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_94 : FrameRectangleCertificate 8250 8500 (507/1000) (203/400) lowTIParameters94 where
  full := (7295017817/62500000000)
  energy := (171391310833/250000000000)
  cov := (75664390889/250000000000)
  schur := (103131197581/100000000000)
  cap := (64334437/62500000000)
  W2 := (677708093419/200000000000)
  V := (308345599/1000000000000)
  mass := (51999867/500000000000)
  rootN := (1015535314901/1000000000000)
  rootB := (8020875077/250000000000)
  rootU := (628896978287/1000000000000)
  rootV := (877988609/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_94.scalar_checked
  centre := fun n hn => lowFull1_94 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy94 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_94.bound (by norm_num) hn lowTIParameters94_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_95 : FrameRectangleCertificate 8250 8500 (203/400) (127/250) lowTIParameters95 where
  full := (2336565523/20000000000)
  energy := (685328922263/1000000000000)
  cov := (302955120351/1000000000000)
  schur := (1031502235239/1000000000000)
  cap := (1030257877/1000000000000)
  W2 := (1692904913861/500000000000)
  V := (77162187/250000000000)
  mass := (25998713/250000000000)
  rootN := (1015628985033/1000000000000)
  rootB := (8024407599/250000000000)
  rootU := (157233569401/250000000000)
  rootV := (17568401977/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_95.scalar_checked
  centre := fun n hn => lowFull1_95 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy95 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_95.bound (by norm_num) hn lowTIParameters95_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_96 : FrameRectangleCertificate 8250 8500 (127/250) (1017/2000) lowTIParameters96 where
  full := (58468356377/500000000000)
  energy := (685092710671/1000000000000)
  cov := (151626338687/500000000000)
  schur := (128961572993/125000000000)
  cap := (1031165683/1000000000000)
  W2 := (211442802607/62500000000)
  V := (308951897/1000000000000)
  mass := (103990309/1000000000000)
  rootN := (40628907619/40000000000)
  rootB := (16055884303/500000000000)
  rootU := (628972829587/1000000000000)
  rootV := (1098564221/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_96.scalar_checked
  centre := fun n hn => lowFull1_96 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy96 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_96.bound (by norm_num) hn lowTIParameters96_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_97 : FrameRectangleCertificate 8250 8500 (1017/2000) (509/1000) lowTIParameters97 where
  full := (117045599823/1000000000000)
  energy := (342428304243/500000000000)
  cov := (303550234623/1000000000000)
  schur := (515941510831/500000000000)
  cap := (64504651/62500000000)
  W2 := (3380365491577/1000000000000)
  V := (154627523/500000000000)
  mass := (103986079/1000000000000)
  rootN := (203163286217/200000000000)
  rootB := (16062957511/500000000000)
  rootU := (78626580527/125000000000)
  rootV := (3517129773/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_97.scalar_checked
  centre := fun n hn => lowFull1_97 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy97 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_97.bound (by norm_num) hn lowTIParameters97_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_98 : FrameRectangleCertificate 8250 8500 (509/1000) (1019/2000) lowTIParameters98 where
  full := (58577471167/500000000000)
  energy := (171155153909/250000000000)
  cov := (303847792097/1000000000000)
  schur := (129009193517/125000000000)
  cap := (1032984093/1000000000000)
  W2 := (1688825879969/500000000000)
  V := (77389549/250000000000)
  mass := (5199107/50000000000)
  rootN := (1015910206729/1000000000000)
  rootB := (16070034949/500000000000)
  rootU := (629053731537/1000000000000)
  rootV := (8797132999/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_98.scalar_checked
  centre := fun n hn => lowFull1_98 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy98 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_98.bound (by norm_num) hn lowTIParameters98_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_99 : FrameRectangleCertificate 8250 8500 (1019/2000) (51/100) lowTIParameters99 where
  full := (29316186327/250000000000)
  energy := (42774045753/62500000000)
  cov := (152072674899/500000000000)
  schur := (1032264163111/1000000000000)
  cap := (1033894719/1000000000000)
  W2 := (3374943629433/1000000000000)
  V := (154930673/500000000000)
  mass := (103978471/1000000000000)
  rootN := (127000502159/125000000000)
  rootB := (32154233299/1000000000000)
  rootU := (629096101669/1000000000000)
  rootV := (17602878913/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_99.scalar_checked
  centre := fun n hn => lowFull1_99 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy99 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_99.bound (by norm_num) hn lowTIParameters99_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_100 : FrameRectangleCertificate 8250 8500 (51/100) (1021/2000) lowTIParameters100 where
  full := (7335938363/62500000000)
  energy := (684148957649/1000000000000)
  cov := (15090565023/50000000000)
  schur := (1023538228169/1000000000000)
  cap := (32153833/31250000000)
  W2 := (3372241082731/1000000000000)
  V := (307483431/1000000000000)
  mass := (103975053/1000000000000)
  rootN := (1011700661347/1000000000000)
  rootB := (16038412141/500000000000)
  rootU := (314569882399/500000000000)
  rootV := (8767602737/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_100.scalar_checked
  centre := fun n hn => lowFull1_100 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy100 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_100.bound (by norm_num) hn lowTIParameters100_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_101 : FrameRectangleCertificate 8250 8500 (1021/2000) (511/1000) lowTIParameters101 where
  full := (5874287647/50000000000)
  energy := (683913292373/1000000000000)
  cov := (302106279477/1000000000000)
  schur := (255931840619/250000000000)
  cap := (1029829959/1000000000000)
  W2 := (3369544102743/1000000000000)
  V := (153891977/500000000000)
  mass := (25992967/250000000000)
  rootN := (505897065241/500000000000)
  rootB := (16045481911/500000000000)
  rootU := (629184731201/1000000000000)
  rootV := (8771886257/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_101.scalar_checked
  centre := fun n hn => lowFull1_101 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy101 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_101.bound (by norm_num) hn lowTIParameters101_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_102 : FrameRectangleCertificate 8250 8500 (511/1000) (1023/2000) lowTIParameters102 where
  full := (117596967847/1000000000000)
  energy := (683677736143/1000000000000)
  cov := (1890007867/6250000000)
  schur := (511958291879/500000000000)
  cap := (4122953/4000000000)
  W2 := (84171316807/25000000000)
  V := (308084477/1000000000000)
  mass := (103968899/1000000000000)
  rootN := (1011887633959/1000000000000)
  rootB := (16052556261/500000000000)
  rootU := (314615505597/500000000000)
  rootV := (4388083843/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_102.scalar_checked
  centre := fun n hn => lowFull1_102 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy102 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_102.bound (by norm_num) hn lowTIParameters102_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_103 : FrameRectangleCertificate 8250 8500 (1023/2000) (64/125) lowTIParameters103 where
  full := (2942716593/25000000000)
  energy := (683442288889/1000000000000)
  cov := (302696238183/1000000000000)
  schur := (512052945869/500000000000)
  cap := (1031647537/1000000000000)
  W2 := (168208338713/50000000000)
  V := (61677/200000000)
  mass := (25991533/250000000000)
  rootN := (1011981171633/1000000000000)
  rootB := (32119270493/1000000000000)
  rootU := (314639307593/500000000000)
  rootV := (3512178811/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_103.scalar_checked
  centre := fun n hn => lowFull1_103 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy103 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_103.bound (by norm_num) hn lowTIParameters103_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_104 : FrameRectangleCertificate 8250 8500 (64/125) (41/80) lowTIParameters104 where
  full := (23564169159/200000000000)
  energy := (683206950541/1000000000000)
  cov := (151495608933/500000000000)
  schur := (1024295286163/1000000000000)
  cap := (516278917/500000000000)
  W2 := (1680743195863/500000000000)
  V := (77171381/250000000000)
  mass := (103963551/1000000000000)
  rootN := (126509342921/125000000000)
  rootB := (32133437943/1000000000000)
  rootU := (125865510733/200000000000)
  rootV := (17569448597/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_104.scalar_checked
  centre := fun n hn => lowFull1_104 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy104 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_104.bound (by norm_num) hn lowTIParameters104_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_105 : FrameRectangleCertificate 8250 8500 (41/80) (513/1000) lowTIParameters105 where
  full := (58966759671/500000000000)
  energy := (341485860513/500000000000)
  cov := (303286197769/1000000000000)
  schur := (16007574481/15625000000)
  cap := (1033469153/1000000000000)
  W2 := (1679405753869/500000000000)
  V := (308986047/1000000000000)
  mass := (20792229/200000000000)
  rootN := (1012168349033/1000000000000)
  rootB := (8036903761/250000000000)
  rootU := (125875567433/200000000000)
  rootV := (4394499737/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_105.scalar_checked
  centre := fun n hn => lowFull1_105 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy105 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_105.bound (by norm_num) hn lowTIParameters105_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_106 : FrameRectangleCertificate 8250 8500 (513/1000) (1027/2000) lowTIParameters106 where
  full := (118046689687/1000000000000)
  energy := (27309464011/40000000000)
  cov := (151790588947/500000000000)
  schur := (51233716669/50000000000)
  cap := (517190751/500000000000)
  W2 := (419517763187/125000000000)
  V := (309286571/1000000000000)
  mass := (1039589/10000000000)
  rootN := (1012261988509/1000000000000)
  rootB := (32161801909/1000000000000)
  rootU := (62942947633/100000000000)
  rootV := (1758654517/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_106.scalar_checked
  centre := fun n hn => lowFull1_106 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy106 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_106.bound (by norm_num) hn lowTIParameters106_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_107 : FrameRectangleCertificate 8250 8500 (1027/2000) (257/500) lowTIParameters107 where
  full := (23632072437/200000000000)
  energy := (136500317643/200000000000)
  cov := (303876158237/1000000000000)
  schur := (512431992833/500000000000)
  cap := (517647449/500000000000)
  W2 := (838369542039/250000000000)
  V := (61917419/200000000000)
  mass := (20791361/200000000000)
  rootN := (506177830823/500000000000)
  rootB := (8043999697/250000000000)
  rootU := (629482481829/1000000000000)
  rootV := (17595087241/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_107.scalar_checked
  centre := fun n hn => lowFull1_107 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy107 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_107.bound (by norm_num) hn lowTIParameters107_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_108 : FrameRectangleCertificate 8250 8500 (257/500) (1029/2000) lowTIParameters108 where
  full := (14784317781/125000000000)
  energy := (85283335597/125000000000)
  cov := (304171138801/1000000000000)
  schur := (1025053723423/1000000000000)
  cap := (1036209349/1000000000000)
  W2 := (1675409839529/500000000000)
  V := (15494381/50000000000)
  mass := (2079097/20000000000)
  rootN := (506224684163/500000000000)
  rootB := (16095102897/500000000000)
  rootU := (314768432223/500000000000)
  rootV := (3520725039/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_108.scalar_checked
  centre := fun n hn => lowFull1_108 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy108 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_108.bound (by norm_num) hn lowTIParameters108_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_109 : FrameRectangleCertificate 8250 8500 (1029/2000) (103/200) lowTIParameters109 where
  full := (29597308831/250000000000)
  energy := (682031889889/1000000000000)
  cov := (304466119583/1000000000000)
  schur := (256310886597/250000000000)
  cap := (259281217/250000000000)
  W2 := (837041655387/250000000000)
  V := (19386759/62500000000)
  mass := (51976513/500000000000)
  rootN := (101254310841/100000000000)
  rootB := (32204423113/1000000000000)
  rootU := (629592635013/1000000000000)
  rootV := (8806079491/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_109.scalar_checked
  centre := fun n hn => lowFull1_109 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy109 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_109.bound (by norm_num) hn lowTIParameters109_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_110 : FrameRectangleCertificate 8250 8500 (103/200) (1031/2000) lowTIParameters110 where
  full := (59252223453/500000000000)
  energy := (681797203479/1000000000000)
  cov := (38095137573/125000000000)
  schur := (256358363579/250000000000)
  cap := (259510367/250000000000)
  W2 := (3345518979007/1000000000000)
  V := (310488669/1000000000000)
  mass := (51975661/500000000000)
  rootN := (126579610221/125000000000)
  rootB := (16109325467/500000000000)
  rootU := (39353112777/62500000000)
  rootV := (3524137733/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_110.scalar_checked
  centre := fun n hn => lowFull1_110 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy110 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_110.bound (by norm_num) hn lowTIParameters110_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_111 : FrameRectangleCertificate 8250 8500 (1031/2000) (129/250) lowTIParameters111 where
  full := (118620182537/1000000000000)
  energy := (340781312741/500000000000)
  cov := (152528040901/500000000000)
  schur := (1025623446979/1000000000000)
  cap := (25973979/25000000000)
  W2 := (3342876735029/1000000000000)
  V := (155394597/500000000000)
  mass := (103949731/1000000000000)
  rootN := (506365344139/500000000000)
  rootB := (6446577883/200000000000)
  rootU := (125941676741/200000000000)
  rootV := (881460711/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_111.scalar_checked
  centre := fun n hn => lowFull1_111 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy111 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_111.bound (by norm_num) hn lowTIParameters111_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_112 : FrameRectangleCertificate 8250 8500 (129/250) (1033/2000) lowTIParameters112 where
  full := (23747289559/200000000000)
  energy := (340664077911/500000000000)
  cov := (152675531619/500000000000)
  schur := (256453381029/250000000000)
  cap := (1039877957/1000000000000)
  W2 := (3340239873073/1000000000000)
  V := (311089719/1000000000000)
  mass := (51974123/500000000000)
  rootN := (506412263901/500000000000)
  rootB := (16123569371/500000000000)
  rootU := (314884191931/500000000000)
  rootV := (8818867827/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_112.scalar_checked
  centre := fun n hn => lowFull1_112 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy112 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_112.bound (by norm_num) hn lowTIParameters112_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_113 : FrameRectangleCertificate 8250 8500 (1033/2000) (517/1000) lowTIParameters113 where
  full := (59426624157/500000000000)
  energy := (681093794431/1000000000000)
  cov := (30564604489/100000000000)
  schur := (256500921373/250000000000)
  cap := (104079787/100000000000)
  W2 := (3337608376829/1000000000000)
  V := (62278049/200000000000)
  mass := (51973429/500000000000)
  rootN := (506459200107/500000000000)
  rootB := (32261399071/1000000000000)
  rootU := (629829816051/1000000000000)
  rootV := (8823126501/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_113.scalar_checked
  centre := fun n hn => lowFull1_113 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy113 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_113.bound (by norm_num) hn lowTIParameters113_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_114 : FrameRectangleCertificate 8250 8500 (517/1000) (207/400) lowTIParameters114 where
  full := (23794117953/200000000000)
  energy := (340429770619/500000000000)
  cov := (305941026759/1000000000000)
  schur := (1026193930869/1000000000000)
  cap := (1041718913/1000000000000)
  W2 := (3334982229979/1000000000000)
  V := (31169077/100000000000)
  mass := (103945561/1000000000000)
  rootN := (1013012305389/1000000000000)
  rootB := (6455134121/200000000000)
  rootU := (314946345731/500000000000)
  rootV := (4413691553/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_114.scalar_checked
  centre := fun n hn => lowFull1_114 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy114 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_114.bound (by norm_num) hn lowTIParameters114_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_115 : FrameRectangleCertificate 8250 8500 (207/400) (259/500) lowTIParameters115 where
  full := (14886059733/125000000000)
  energy := (680625396173/1000000000000)
  cov := (76559002211/250000000000)
  schur := (1026384259999/1000000000000)
  cap := (521320549/500000000000)
  W2 := (1666180708127/500000000000)
  V := (304679/976562500)
  mass := (103944349/1000000000000)
  rootN := (202621248639/200000000000)
  rootB := (6457990703/200000000000)
  rootU := (125991404271/200000000000)
  rootV := (4415818837/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_115.scalar_checked
  centre := fun n hn => lowFull1_115 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy115 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_115.bound (by norm_num) hn lowTIParameters115_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_116 : FrameRectangleCertificate 8250 8500 (259/500) (1037/2000) lowTIParameters116 where
  full := (59603459189/500000000000)
  energy := (680391359169/1000000000000)
  cov := (306530991143/1000000000000)
  schur := (1026574672661/1000000000000)
  cap := (1043564437/1000000000000)
  W2 := (3329745919559/1000000000000)
  V := (156145911/500000000000)
  mass := (6496451/62500000000)
  rootN := (1013200213513/1000000000000)
  rootB := (8076061993/250000000000)
  rootU := (630022817089/1000000000000)
  rootV := (8835890193/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_116.scalar_checked
  centre := fun n hn => lowFull1_116 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy116 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_116.bound (by norm_num) hn lowTIParameters116_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_117 : FrameRectangleCertificate 8250 8500 (1037/2000) (519/1000) lowTIParameters117 where
  full := (119325917113/1000000000000)
  energy := (13603148603/20000000000)
  cov := (15341298683/50000000000)
  schur := (513382584299/500000000000)
  cap := (522244473/500000000000)
  W2 := (1663567861841/500000000000)
  V := (78148087/250000000000)
  mass := (103942157/1000000000000)
  rootN := (1013294216207/1000000000000)
  rootB := (32318554207/1000000000000)
  rootU := (630090090057/1000000000000)
  rootV := (17680281333/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_117.scalar_checked
  centre := fun n hn => lowFull1_117 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy117 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_117.bound (by norm_num) hn lowTIParameters117_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_118 : FrameRectangleCertificate 8250 8500 (519/1000) (1039/2000) lowTIParameters118 where
  full := (14930684991/125000000000)
  energy := (169980902263/250000000000)
  cov := (307120956389/1000000000000)
  schur := (256738936897/250000000000)
  cap := (130676829/125000000000)
  W2 := (132981232507/40000000000)
  V := (2503143/8000000000)
  mass := (51970583/500000000000)
  rootN := (25334706279/25000000000)
  rootB := (32332872313/1000000000000)
  rootU := (157539712941/250000000000)
  rootV := (17688778223/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_118.scalar_checked
  centre := fun n hn => lowFull1_118 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy118 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_118.bound (by norm_num) hn lowTIParameters118_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_119 : FrameRectangleCertificate 8250 8500 (1039/2000) (13/25) lowTIParameters119 where
  full := (4782624509/40000000000)
  energy := (135937979161/200000000000)
  cov := (76853984833/250000000000)
  schur := (256786602349/250000000000)
  cap := (1046341511/1000000000000)
  W2 := (3321931170547/1000000000000)
  V := (156596701/500000000000)
  mass := (1299253/12500000000)
  rootN := (506741159123/500000000000)
  rootB := (32347202523/1000000000000)
  rootU := (126045822753/200000000000)
  rootV := (17697271033/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_119.scalar_checked
  centre := fun n hn => lowFull1_119 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy119 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_119.bound (by norm_num) hn lowTIParameters119_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_120 : FrameRectangleCertificate 8250 8500 (13/25) (1041/2000) lowTIParameters120 where
  full := (29921580363/250000000000)
  energy := (135891258067/200000000000)
  cov := (152530196797/500000000000)
  schur := (254624048393/250000000000)
  cap := (130168821/125000000000)
  W2 := (3319336781351/1000000000000)
  V := (310793587/1000000000000)
  mass := (103939373/1000000000000)
  rootN := (252301431027/250000000000)
  rootB := (8067490967/250000000000)
  rootU := (78787610961/125000000000)
  rootV := (8814669407/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_120.scalar_checked
  centre := fun n hn => lowFull1_120 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy120 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_120.bound (by norm_num) hn lowTIParameters120_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_121 : FrameRectangleCertificate 8250 8500 (1041/2000) (521/1000) lowTIParameters121 where
  full := (1198076121/10000000000)
  energy := (5306428067/7812500000)
  cov := (38169103649/125000000000)
  schur := (203737073807/200000000000)
  cap := (208454939/200000000000)
  W2 := (3316747629259/1000000000000)
  V := (155545759/500000000000)
  mass := (51969281/500000000000)
  rootN := (504649722341/500000000000)
  rootB := (32284279379/1000000000000)
  rootU := (630374185227/1000000000000)
  rootV := (17637786653/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_121.scalar_checked
  centre := fun n hn => lowFull1_121 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy121 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_121.bound (by norm_num) hn lowTIParameters121_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_122 : FrameRectangleCertificate 8250 8500 (521/1000) (1043/2000) lowTIParameters122 where
  full := (119929490713/1000000000000)
  energy := (339494701229/500000000000)
  cov := (305645264999/1000000000000)
  schur := (10188746259/10000000000)
  cap := (1043200059/1000000000000)
  W2 := (331416369849/100000000000)
  V := (6227789/20000000000)
  mass := (103937803/1000000000000)
  rootN := (1009393196877/1000000000000)
  rootB := (6459721539/200000000000)
  rootU := (630449018161/1000000000000)
  rootV := (4411557619/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_122.scalar_checked
  centre := fun n hn => lowFull1_122 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy122 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_122.bound (by norm_num) hn lowTIParameters122_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_123 : FrameRectangleCertificate 8250 8500 (1043/2000) (261/500) lowTIParameters123 where
  full := (120051963379/1000000000000)
  energy := (84844514989/125000000000)
  cov := (305937701019/1000000000000)
  schur := (509531981977/500000000000)
  cap := (261031667/250000000000)
  W2 := (1655792486661/500000000000)
  V := (155843691/500000000000)
  mass := (103937093/1000000000000)
  rootN := (1009486980577/1000000000000)
  rootB := (16156474461/500000000000)
  rootU := (315262699167/500000000000)
  rootV := (17654670261/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_123.scalar_checked
  centre := fun n hn => lowFull1_123 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy123 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_123.bound (by norm_num) hn lowTIParameters123_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_124 : FrameRectangleCertificate 8250 8500 (261/500) (209/400) lowTIParameters124 where
  full := (60087518117/500000000000)
  energy := (678522944871/1000000000000)
  cov := (9569691789/31250000000)
  schur := (1019253382963/1000000000000)
  cap := (522527269/500000000000)
  W2 := (3309011438153/1000000000000)
  V := (155992657/500000000000)
  mass := (103936427/1000000000000)
  rootN := (1009580795659/1000000000000)
  rootB := (3232730329/100000000000)
  rootU := (630603337669/1000000000000)
  rootV := (17663106013/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_124.scalar_checked
  centre := fun n hn => lowFull1_124 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy124 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_124.bound (by norm_num) hn lowTIParameters124_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_125 : FrameRectangleCertificate 8250 8500 (209/400) (523/1000) lowTIParameters125 where
  full := (60149357729/500000000000)
  energy := (33914493863/50000000000)
  cov := (306522573683/1000000000000)
  schur := (40777715307/40000000000)
  cap := (261495921/250000000000)
  W2 := (3306443077299/1000000000000)
  V := (156141623/500000000000)
  mass := (20787161/200000000000)
  rootN := (1009674641989/1000000000000)
  rootB := (6468334203/200000000000)
  rootU := (630682848137/1000000000000)
  rootV := (8835768869/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_125.scalar_checked
  centre := fun n hn => lowFull1_125 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy125 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_125.bound (by norm_num) hn lowTIParameters125_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_126 : FrameRectangleCertificate 8250 8500 (523/1000) (1047/2000) lowTIParameters126 where
  full := (60211503641/500000000000)
  energy := (84757114627/125000000000)
  cov := (306815010331/1000000000000)
  schur := (509816231453/500000000000)
  cap := (523457057/500000000000)
  W2 := (3303879875299/1000000000000)
  V := (312581179/1000000000000)
  mass := (103935221/1000000000000)
  rootN := (1009768519467/1000000000000)
  rootB := (32356052201/1000000000000)
  rootU := (315381970903/500000000000)
  rootV := (1767996547/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_126.scalar_checked
  centre := fun n hn => lowFull1_126 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy126 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_126.bound (by norm_num) hn lowTIParameters126_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_127 : FrameRectangleCertificate 8250 8500 (1047/2000) (131/250) lowTIParameters127 where
  full := (60273958993/500000000000)
  energy := (169456016017/250000000000)
  cov := (61421489437/200000000000)
  schur := (203964424679/200000000000)
  cap := (1047845847/1000000000000)
  W2 := (412665227083/125000000000)
  V := (39109889/125000000000)
  mass := (4157387/40000000000)
  rootN := (201972485591/200000000000)
  rootB := (8092611781/250000000000)
  rootU := (78855828851/125000000000)
  rootV := (17688389187/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_127.scalar_checked
  centre := fun n hn => lowFull1_127 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy127 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_127.bound (by norm_num) hn lowTIParameters127_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_128 : FrameRectangleCertificate 8250 8500 (131/250) (1049/2000) lowTIParameters128 where
  full := (120673453897/1000000000000)
  energy := (338795659173/500000000000)
  cov := (38424985531/125000000000)
  schur := (127501482993/125000000000)
  cap := (1048778897/1000000000000)
  W2 := (659753777197/200000000000)
  V := (62635409/200000000000)
  mass := (103934163/1000000000000)
  rootN := (1009956367347/1000000000000)
  rootB := (32384855983/1000000000000)
  rootU := (126186185469/200000000000)
  rootV := (8848404447/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_128.scalar_checked
  centre := fun n hn => lowFull1_128 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy128 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_128.bound (by norm_num) hn lowTIParameters128_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_129 : FrameRectangleCertificate 8250 8500 (1049/2000) (21/40) lowTIParameters129 where
  full := (24159924277/200000000000)
  energy := (338679339891/500000000000)
  cov := (307692321519/1000000000000)
  schur := (1020201684317/1000000000000)
  cap := (1049713273/1000000000000)
  W2 := (1648110533957/500000000000)
  V := (156737489/500000000000)
  mass := (103933683/1000000000000)
  rootN := (1010050337517/1000000000000)
  rootB := (32399278897/1000000000000)
  rootU := (315508421839/500000000000)
  rootV := (17705224597/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_129.scalar_checked
  centre := fun n hn => lowFull1_129 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy129 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_129.bound (by norm_num) hn lowTIParameters129_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_130 : FrameRectangleCertificate 8250 8500 (21/40) (1051/2000) lowTIParameters130 where
  full := (120926426877/1000000000000)
  energy := (677126148311/1000000000000)
  cov := (61596951799/200000000000)
  schur := (1020391584307/1000000000000)
  cap := (525324497/500000000000)
  W2 := (823419586809/250000000000)
  V := (19610807/62500000000)
  mass := (51966617/500000000000)
  rootN := (505072169177/500000000000)
  rootB := (1620685807/50000000000)
  rootU := (78888049021/125000000000)
  rootV := (1771363633/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_130.scalar_checked
  centre := fun n hn => lowFull1_130 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy130 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_130.bound (by norm_num) hn lowTIParameters130_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_131 : FrameRectangleCertificate 8250 8500 (1051/2000) (263/500) lowTIParameters131 where
  full := (3026346921/25000000000)
  energy := (676893723859/1000000000000)
  cov := (308277196679/1000000000000)
  schur := (1020581563667/1000000000000)
  cap := (131448259/125000000000)
  W2 := (1645570354317/500000000000)
  V := (62814169/200000000000)
  mass := (25983203/250000000000)
  rootN := (1010238369727/1000000000000)
  rootB := (810704197/25000000000)
  rootU := (631193585207/1000000000000)
  rootV := (8861022021/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_131.scalar_checked
  centre := fun n hn => lowFull1_131 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy131 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_131.bound (by norm_num) hn lowTIParameters131_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_132 : FrameRectangleCertificate 8250 8500 (263/500) (1053/2000) lowTIParameters132 where
  full := (605909889/5000000000)
  energy := (676661406363/1000000000000)
  cov := (308569634569/1000000000000)
  schur := (1020771622217/1000000000000)
  cap := (526262261/500000000000)
  W2 := (65772162741/20000000000)
  V := (314368779/1000000000000)
  mass := (103932417/1000000000000)
  rootN := (505166215769/500000000000)
  rootB := (16221317163/500000000000)
  rootU := (78910554413/125000000000)
  rootV := (3546089559/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_132.scalar_checked
  centre := fun n hn => lowFull1_132 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy132 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_132.bound (by norm_num) hn lowTIParameters132_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_133 : FrameRectangleCertificate 8250 8500 (1053/2000) (527/1000) lowTIParameters133 where
  full := (379096051/3125000000)
  energy := (84553649469/125000000000)
  cov := (38607759083/125000000000)
  schur := (510480879851/500000000000)
  cap := (1053464357/1000000000000)
  W2 := (1643040308653/500000000000)
  V := (314666713/1000000000000)
  mass := (51966023/500000000000)
  rootN := (505213261827/500000000000)
  rootB := (32457115661/1000000000000)
  rootU := (63137695499/100000000000)
  rootV := (17738847567/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_133.scalar_checked
  centre := fun n hn => lowFull1_133 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy133 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_133.bound (by norm_num) hn lowTIParameters133_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_134 : FrameRectangleCertificate 8250 8500 (527/1000) (211/400) lowTIParameters134 where
  full := (60720079511/500000000000)
  energy := (16904927299/25000000000)
  cov := (61830902193/200000000000)
  schur := (510575987967/500000000000)
  cap := (527202797/500000000000)
  W2 := (1641779067221/500000000000)
  V := (314964647/1000000000000)
  mass := (103931699/1000000000000)
  rootN := (252630161493/250000000000)
  rootB := (16235806063/500000000000)
  rootU := (631471156907/1000000000000)
  rootV := (4436810841/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_134.scalar_checked
  centre := fun n hn => lowFull1_134 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy134 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_134.bound (by norm_num) hn lowTIParameters134_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_135 : FrameRectangleCertificate 8250 8500 (211/400) (66/125) lowTIParameters135 where
  full := (30392563143/250000000000)
  energy := (135193018983/200000000000)
  cov := (30944694947/100000000000)
  schur := (510671135337/500000000000)
  cap := (527674123/500000000000)
  W2 := (3281040673403/1000000000000)
  V := (157631291/500000000000)
  mass := (103931373/1000000000000)
  rootN := (202122959673/200000000000)
  rootB := (324861239/10000000000)
  rootU := (78945881717/125000000000)
  rootV := (17755635219/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_135.scalar_checked
  centre := fun n hn => lowFull1_135 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy135 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_135.bound (by norm_num) hn lowTIParameters135_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_136 : FrameRectangleCertificate 8250 8500 (66/125) (1057/2000) lowTIParameters136 where
  full := (12170102369/100000000000)
  energy := (84466650569/125000000000)
  cov := (15486969409/50000000000)
  schur := (1021532643721/1000000000000)
  cap := (1056292327/1000000000000)
  W2 := (3278528219311/1000000000000)
  V := (315560517/1000000000000)
  mass := (51965533/500000000000)
  rootN := (1010708980727/1000000000000)
  rootB := (32500651179/1000000000000)
  rootU := (315832329127/500000000000)
  rootV := (17764023109/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_136.scalar_checked
  centre := fun n hn => lowFull1_136 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy136 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_136.bound (by norm_num) hn lowTIParameters136_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_137 : FrameRectangleCertificate 8250 8500 (1057/2000) (529/1000) lowTIParameters137 where
  full := (15229059893/125000000000)
  energy := (675501420803/1000000000000)
  cov := (155015913547/500000000000)
  schur := (20434461897/20000000000)
  cap := (528618927/500000000000)
  W2 := (1638010378649/500000000000)
  V := (315858451/1000000000000)
  mass := (103930779/1000000000000)
  rootN := (1010803192937/1000000000000)
  rootB := (32515194203/1000000000000)
  rootU := (9871312239/15625000000)
  rootV := (4443101753/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_137.scalar_checked
  centre := fun n hn => lowFull1_137 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy137 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_137.bound (by norm_num) hn lowTIParameters137_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_138 : FrameRectangleCertificate 8250 8500 (529/1000) (1059/2000) lowTIParameters138 where
  full := (24392925149/200000000000)
  energy := (675269743601/1000000000000)
  cov := (310324266209/1000000000000)
  schur := (20438272477/20000000000)
  cap := (1058184839/1000000000000)
  W2 := (654703654521/200000000000)
  V := (316156387/1000000000000)
  mass := (10393051/100000000000)
  rootN := (505448717441/500000000000)
  rootB := (6505950627/200000000000)
  rootU := (78983130219/125000000000)
  rootV := (17780787019/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_138.scalar_checked
  centre := fun n hn => lowFull1_138 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy138 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_138.bound (by norm_num) hn lowTIParameters138_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_139 : FrameRectangleCertificate 8250 8500 (1059/2000) (53/100) lowTIParameters139 where
  full := (61048735183/500000000000)
  energy := (168759543219/250000000000)
  cov := (38827088191/125000000000)
  schur := (102210423051/100000000000)
  cap := (529566649/500000000000)
  W2 := (1635510375213/500000000000)
  V := (158227161/500000000000)
  mass := (103930257/1000000000000)
  rootN := (20219834129/20000000000)
  rootB := (32544328201/1000000000000)
  rootU := (126393569321/200000000000)
  rootV := (355783261/20000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_139.scalar_checked
  centre := fun n hn => lowFull1_139 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy139 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_139.bound (by norm_num) hn lowTIParameters139_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_140 : FrameRectangleCertificate 8250 8500 (53/100) (1061/2000) lowTIParameters140 where
  full := (4889240797/40000000000)
  energy := (134961341713/200000000000)
  cov := (308239948467/1000000000000)
  schur := (1013526873823/1000000000000)
  cap := (527064803/500000000000)
  W2 := (653705635231/200000000000)
  V := (314032897/1000000000000)
  mass := (103930019/1000000000000)
  rootN := (1006740718271/1000000000000)
  rootB := (16233681083/500000000000)
  rootU := (79009051363/125000000000)
  rootV := (3544194673/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_140.scalar_checked
  centre := fun n hn => lowFull1_140 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy140 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_140.bound (by norm_num) hn lowTIParameters140_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_141 : FrameRectangleCertificate 8250 8500 (1061/2000) (531/1000) lowTIParameters141 where
  full := (122365281393/1000000000000)
  energy := (168643837649/250000000000)
  cov := (308529870833/1000000000000)
  schur := (1013715990043/1000000000000)
  cap := (1055075967/1000000000000)
  W2 := (3266040535119/1000000000000)
  V := (78582067/250000000000)
  mass := (25982449/250000000000)
  rootN := (503417319439/500000000000)
  rootB := (32481932933/1000000000000)
  rootU := (316089373881/500000000000)
  rootV := (3545861069/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_141.scalar_checked
  centre := fun n hn => lowFull1_141 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy141 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_141.bound (by norm_num) hn lowTIParameters141_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_142 : FrameRectangleCertificate 8250 8500 (531/1000) (1063/2000) lowTIParameters142 where
  full := (6125013089/50000000000)
  energy := (134868819781/200000000000)
  cov := (308819793397/1000000000000)
  schur := (1013905182627/1000000000000)
  cap := (1056023849/1000000000000)
  W2 := (3263557812789/1000000000000)
  V := (314623639/1000000000000)
  mass := (51964793/500000000000)
  rootN := (251732147161/250000000000)
  rootB := (4062065071/125000000000)
  rootU := (316143435169/500000000000)
  rootV := (17737633411/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_142.scalar_checked
  centre := fun n hn => lowFull1_142 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy142 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_142.bound (by norm_num) hn lowTIParameters142_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_143 : FrameRectangleCertificate 8250 8500 (1063/2000) (133/250) lowTIParameters143 where
  full := (15329496021/125000000000)
  energy := (674112953423/1000000000000)
  cov := (965967863/3125000000)
  schur := (253523612841/250000000000)
  cap := (1056973267/1000000000000)
  W2 := (1630539997313/500000000000)
  V := (314919011/1000000000000)
  mass := (103929389/1000000000000)
  rootN := (31469455233/31250000000)
  rootB := (32511125281/1000000000000)
  rootU := (632396791907/1000000000000)
  rootV := (17745957597/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_143.scalar_checked
  centre := fun n hn => lowFull1_143 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy143 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_143.bound (by norm_num) hn lowTIParameters143_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_144 : FrameRectangleCertificate 8250 8500 (133/250) (213/400) lowTIParameters144 where
  full := (30693101919/250000000000)
  energy := (336940957041/500000000000)
  cov := (309399639121/1000000000000)
  schur := (507141898029/500000000000)
  cap := (528962119/500000000000)
  W2 := (3258607066181/1000000000000)
  V := (157607191/500000000000)
  mass := (25982301/250000000000)
  rootN := (125889571901/125000000000)
  rootB := (32525747309/1000000000000)
  rootU := (632508525781/1000000000000)
  rootV := (17754277851/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_144.scalar_checked
  centre := fun n hn => lowFull1_144 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy144 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_144.bound (by norm_num) hn lowTIParameters144_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_145 : FrameRectangleCertificate 8250 8500 (213/400) (533/1000) lowTIParameters145 where
  full := (7681849217/62500000000)
  energy := (673650980819/1000000000000)
  cov := (309689562281/1000000000000)
  schur := (202894643301/200000000000)
  cap := (1058876777/1000000000000)
  W2 := (651227802619/200000000000)
  V := (157754877/500000000000)
  mass := (10392903/100000000000)
  rootN := (62950663237/62500000000)
  rootB := (32540386861/1000000000000)
  rootU := (632622085333/1000000000000)
  rootV := (17762594237/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_145.scalar_checked
  centre := fun n hn => lowFull1_145 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy145 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_145.bound (by norm_num) hn lowTIParameters145_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_146 : FrameRectangleCertificate 8250 8500 (533/1000) (1067/2000) lowTIParameters146 where
  full := (61523757393/500000000000)
  energy := (336710076781/500000000000)
  cov := (309979485639/1000000000000)
  schur := (507331356247/500000000000)
  cap := (1059830899/1000000000000)
  W2 := (3253675820981/1000000000000)
  V := (157902563/500000000000)
  mass := (103928867/1000000000000)
  rootN := (503652338547/500000000000)
  rootB := (32555044141/1000000000000)
  rootU := (316368742013/500000000000)
  rootV := (1777090673/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_146.scalar_checked
  centre := fun n hn => lowFull1_146 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy146 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_146.bound (by norm_num) hn lowTIParameters146_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_147 : FrameRectangleCertificate 8250 8500 (1067/2000) (267/500) lowTIParameters147 where
  full := (123186196897/1000000000000)
  energy := (2692757729/4000000000)
  cov := (155134704597/500000000000)
  schur := (507426141919/500000000000)
  cap := (530393311/500000000000)
  W2 := (650243495129/200000000000)
  V := (316100499/1000000000000)
  mass := (103928713/1000000000000)
  rootN := (1007398771013/1000000000000)
  rootB := (8142429851/250000000000)
  rootU := (316427367697/500000000000)
  rootV := (8889607683/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_147.scalar_checked
  centre := fun n hn => lowFull1_147 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy147 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_147.bound (by norm_num) hn lowTIParameters147_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_148 : FrameRectangleCertificate 8250 8500 (267/500) (1069/2000) lowTIParameters148 where
  full := (61662820563/500000000000)
  energy := (168239704203/250000000000)
  cov := (62111866589/200000000000)
  schur := (507520965159/500000000000)
  cap := (26543599/25000000000)
  W2 := (406095495349/125000000000)
  V := (316395871/1000000000000)
  mass := (103928569/1000000000000)
  rootN := (503746446717/500000000000)
  rootB := (32584412839/1000000000000)
  rootU := (316486926499/500000000000)
  rootV := (4446880023/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_148.scalar_checked
  centre := fun n hn => lowFull1_148 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy148 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_148.bound (by norm_num) hn lowTIParameters148_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_149 : FrameRectangleCertificate 8250 8500 (1069/2000) (107/200) lowTIParameters149 where
  full := (123465854861/1000000000000)
  energy := (336364153591/500000000000)
  cov := (310849256891/1000000000000)
  schur := (1015231651729/1000000000000)
  cap := (106270293/100000000000)
  W2 := (3246315268271/1000000000000)
  V := (79172811/250000000000)
  mass := (103928433/1000000000000)
  rootN := (201517408849/200000000000)
  rootB := (16299562341/500000000000)
  rootU := (633094850513/1000000000000)
  rootV := (17795820971/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_149.scalar_checked
  centre := fun n hn => lowFull1_149 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy149 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_149.bound (by norm_num) hn lowTIParameters149_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_150 : FrameRectangleCertificate 8250 8500 (107/200) (1071/2000) lowTIParameters150 where
  full := (123606845533/1000000000000)
  energy := (10507779739/15625000000)
  cov := (77784795259/250000000000)
  schur := (1015421447899/1000000000000)
  cap := (265915887/250000000000)
  W2 := (50685490281/15625000000)
  V := (316986617/1000000000000)
  mass := (20785661/200000000000)
  rootN := (503840611677/500000000000)
  rootB := (16306927577/500000000000)
  rootU := (79152217707/125000000000)
  rootV := (17804117979/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_150.scalar_checked
  centre := fun n hn => lowFull1_150 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy150 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_150.bound (by norm_num) hn lowTIParameters150_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_151 : FrameRectangleCertificate 8250 8500 (1071/2000) (67/125) lowTIParameters151 where
  full := (123748620633/1000000000000)
  energy := (134453521017/200000000000)
  cov := (311429105373/1000000000000)
  schur := (1015611318599/1000000000000)
  cap := (1064625829/1000000000000)
  W2 := (3241432277889/1000000000000)
  V := (31728199/100000000000)
  mass := (20785637/200000000000)
  rootN := (1007775430639/1000000000000)
  rootB := (1631430223/50000000000)
  rootU := (63334254023/100000000000)
  rootV := (17812411123/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_151.scalar_checked
  centre := fun n hn => lowFull1_151 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy151 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_151.bound (by norm_num) hn lowTIParameters151_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_152 : FrameRectangleCertificate 8250 8500 (67/125) (1073/2000) lowTIParameters152 where
  full := (30972796923/250000000000)
  energy := (336018706243/500000000000)
  cov := (62343805981/200000000000)
  schur := (31743789489/31250000000)
  cap := (33299681/31250000000)
  W2 := (3238997953981/1000000000000)
  V := (317577363/1000000000000)
  mass := (12991009/125000000000)
  rootN := (1007869666003/1000000000000)
  rootB := (6528674573/200000000000)
  rootU := (158367315017/250000000000)
  rootV := (2227587551/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_152.scalar_checked
  centre := fun n hn => lowFull1_152 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy152 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_152.bound (by norm_num) hn lowTIParameters152_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_153 : FrameRectangleCertificate 8250 8500 (1073/2000) (537/1000) lowTIParameters153 where
  full := (124034554309/1000000000000)
  energy := (167951831357/250000000000)
  cov := (312008954631/1000000000000)
  schur := (1015991282831/1000000000000)
  cap := (1066555451/1000000000000)
  W2 := (3236568392273/1000000000000)
  V := (9933523/31250000000)
  mass := (20785593/200000000000)
  rootN := (1007963929331/1000000000000)
  rootB := (16329080279/500000000000)
  rootU := (316798957553/500000000000)
  rootV := (8914492919/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_153.scalar_checked
  centre := fun n hn => lowFull1_153 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy153 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_153.bound (by norm_num) hn lowTIParameters153_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_154 : FrameRectangleCertificate 8250 8500 (537/1000) (43/80) lowTIParameters154 where
  full := (124178728127/1000000000000)
  energy := (13431546877/20000000000)
  cov := (4879669993/15625000000)
  schur := (508090687989/500000000000)
  cap := (533761413/500000000000)
  W2 := (3234143578939/1000000000000)
  V := (31816811/100000000000)
  mass := (20785573/200000000000)
  rootN := (100805822053/100000000000)
  rootB := (16336483909/500000000000)
  rootU := (633728519331/1000000000000)
  rootV := (2229658431/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_154.scalar_checked
  centre := fun n hn => lowFull1_154 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy154 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_154.bound (by norm_num) hn lowTIParameters154_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_155 : FrameRectangleCertificate 8250 8500 (43/80) (269/500) lowTIParameters155 where
  full := (62161858423/500000000000)
  energy := (671347467681/1000000000000)
  cov := (62517760933/200000000000)
  schur := (508185771431/500000000000)
  cap := (106849193/100000000000)
  W2 := (807930875021/250000000000)
  V := (79615871/250000000000)
  mass := (103927771/1000000000000)
  rootN := (504076269741/500000000000)
  rootB := (16343897409/500000000000)
  rootU := (79232635849/125000000000)
  rootV := (3569109043/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_155.scalar_checked
  centre := fun n hn => lowFull1_155 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy155 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_155.bound (by norm_num) hn lowTIParameters155_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_156 : FrameRectangleCertificate 8250 8500 (269/500) (1077/2000) lowTIParameters156 where
  full := (24893905643/200000000000)
  energy := (33555884843/50000000000)
  cov := (312878729973/1000000000000)
  schur := (25414044583/25000000000)
  cap := (534731391/500000000000)
  W2 := (3229308141969/1000000000000)
  V := (159379429/500000000000)
  mass := (51963841/500000000000)
  rootN := (201649377219/200000000000)
  rootB := (1635132091/50000000000)
  rootU := (158498907901/250000000000)
  rootV := (2231727393/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_156.scalar_checked
  centre := fun n hn => lowFull1_156 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy156 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_156.bound (by norm_num) hn lowTIParameters156_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_157 : FrameRectangleCertificate 8250 8500 (1077/2000) (539/1000) lowTIParameters157 where
  full := (24923234009/200000000000)
  energy := (670888031319/1000000000000)
  cov := (19573040967/62500000000)
  schur := (1016752097143/1000000000000)
  cap := (1070435397/1000000000000)
  W2 := (1613448745437/500000000000)
  V := (39881779/125000000000)
  mass := (103927599/1000000000000)
  rootN := (1008341260261/1000000000000)
  rootB := (32717509029/1000000000000)
  rootU := (15853304199/25000000000)
  rootV := (446552231/25000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_157.scalar_checked
  centre := fun n hn => lowFull1_157 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy157 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_157.bound (by norm_num) hn lowTIParameters157_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_158 : FrameRectangleCertificate 8250 8500 (539/1000) (1079/2000) lowTIParameters158 where
  full := (62381825097/500000000000)
  energy := (670658470991/1000000000000)
  cov := (313458581161/1000000000000)
  schur := (1016942484127/1000000000000)
  cap := (267852449/250000000000)
  W2 := (3224491533083/1000000000000)
  V := (319349607/1000000000000)
  mass := (649547/6250000000)
  rootN := (252108915467/250000000000)
  rootB := (6546479347/200000000000)
  rootU := (317135355049/500000000000)
  rootV := (17870355537/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_158.scalar_checked
  centre := fun n hn => lowFull1_158 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy158 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_158.bound (by norm_num) hn lowTIParameters158_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle1_159 : FrameRectangleCertificate 8250 8500 (1079/2000) (27/50) lowTIParameters159 where
  full := (62455988289/500000000000)
  energy := (670429015813/1000000000000)
  cov := (78437126761/250000000000)
  schur := (203426588819/200000000000)
  cap := (536192997/500000000000)
  W2 := (1611045127499/500000000000)
  V := (319644981/1000000000000)
  mass := (51963723/500000000000)
  rootN := (1008530090823/1000000000000)
  rootB := (16373652571/500000000000)
  rootU := (126882254467/200000000000)
  rootV := (139676703/7812500000)
  nonneg := by norm_num
  scalar := lowFrameWitness1_159.scalar_checked
  centre := fun n hn => lowFull1_159 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy159 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness1_159.bound (by norm_num) hn lowTIParameters159_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangles1 (j : Fin 160) :
    FrameRectangleCertificate 8250 8500 (frameNoiseLower j) (frameNoiseUpper j) (lowTIParameters j) := by
  match j with
  | ⟨0,_⟩ => convert lowRectangle1_0 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨1,_⟩ => convert lowRectangle1_1 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨2,_⟩ => convert lowRectangle1_2 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨3,_⟩ => convert lowRectangle1_3 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨4,_⟩ => convert lowRectangle1_4 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨5,_⟩ => convert lowRectangle1_5 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨6,_⟩ => convert lowRectangle1_6 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨7,_⟩ => convert lowRectangle1_7 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨8,_⟩ => convert lowRectangle1_8 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨9,_⟩ => convert lowRectangle1_9 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨10,_⟩ => convert lowRectangle1_10 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨11,_⟩ => convert lowRectangle1_11 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨12,_⟩ => convert lowRectangle1_12 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨13,_⟩ => convert lowRectangle1_13 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨14,_⟩ => convert lowRectangle1_14 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨15,_⟩ => convert lowRectangle1_15 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨16,_⟩ => convert lowRectangle1_16 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨17,_⟩ => convert lowRectangle1_17 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨18,_⟩ => convert lowRectangle1_18 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨19,_⟩ => convert lowRectangle1_19 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨20,_⟩ => convert lowRectangle1_20 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨21,_⟩ => convert lowRectangle1_21 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨22,_⟩ => convert lowRectangle1_22 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨23,_⟩ => convert lowRectangle1_23 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨24,_⟩ => convert lowRectangle1_24 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨25,_⟩ => convert lowRectangle1_25 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨26,_⟩ => convert lowRectangle1_26 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨27,_⟩ => convert lowRectangle1_27 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨28,_⟩ => convert lowRectangle1_28 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨29,_⟩ => convert lowRectangle1_29 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨30,_⟩ => convert lowRectangle1_30 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨31,_⟩ => convert lowRectangle1_31 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨32,_⟩ => convert lowRectangle1_32 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨33,_⟩ => convert lowRectangle1_33 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨34,_⟩ => convert lowRectangle1_34 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨35,_⟩ => convert lowRectangle1_35 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨36,_⟩ => convert lowRectangle1_36 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨37,_⟩ => convert lowRectangle1_37 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨38,_⟩ => convert lowRectangle1_38 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨39,_⟩ => convert lowRectangle1_39 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨40,_⟩ => convert lowRectangle1_40 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨41,_⟩ => convert lowRectangle1_41 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨42,_⟩ => convert lowRectangle1_42 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨43,_⟩ => convert lowRectangle1_43 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨44,_⟩ => convert lowRectangle1_44 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨45,_⟩ => convert lowRectangle1_45 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨46,_⟩ => convert lowRectangle1_46 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨47,_⟩ => convert lowRectangle1_47 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨48,_⟩ => convert lowRectangle1_48 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨49,_⟩ => convert lowRectangle1_49 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨50,_⟩ => convert lowRectangle1_50 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨51,_⟩ => convert lowRectangle1_51 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨52,_⟩ => convert lowRectangle1_52 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨53,_⟩ => convert lowRectangle1_53 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨54,_⟩ => convert lowRectangle1_54 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨55,_⟩ => convert lowRectangle1_55 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨56,_⟩ => convert lowRectangle1_56 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨57,_⟩ => convert lowRectangle1_57 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨58,_⟩ => convert lowRectangle1_58 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨59,_⟩ => convert lowRectangle1_59 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨60,_⟩ => convert lowRectangle1_60 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨61,_⟩ => convert lowRectangle1_61 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨62,_⟩ => convert lowRectangle1_62 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨63,_⟩ => convert lowRectangle1_63 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨64,_⟩ => convert lowRectangle1_64 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨65,_⟩ => convert lowRectangle1_65 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨66,_⟩ => convert lowRectangle1_66 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨67,_⟩ => convert lowRectangle1_67 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨68,_⟩ => convert lowRectangle1_68 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨69,_⟩ => convert lowRectangle1_69 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨70,_⟩ => convert lowRectangle1_70 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨71,_⟩ => convert lowRectangle1_71 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨72,_⟩ => convert lowRectangle1_72 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨73,_⟩ => convert lowRectangle1_73 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨74,_⟩ => convert lowRectangle1_74 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨75,_⟩ => convert lowRectangle1_75 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨76,_⟩ => convert lowRectangle1_76 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨77,_⟩ => convert lowRectangle1_77 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨78,_⟩ => convert lowRectangle1_78 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨79,_⟩ => convert lowRectangle1_79 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨80,_⟩ => convert lowRectangle1_80 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨81,_⟩ => convert lowRectangle1_81 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨82,_⟩ => convert lowRectangle1_82 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨83,_⟩ => convert lowRectangle1_83 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨84,_⟩ => convert lowRectangle1_84 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨85,_⟩ => convert lowRectangle1_85 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨86,_⟩ => convert lowRectangle1_86 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨87,_⟩ => convert lowRectangle1_87 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨88,_⟩ => convert lowRectangle1_88 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨89,_⟩ => convert lowRectangle1_89 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨90,_⟩ => convert lowRectangle1_90 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨91,_⟩ => convert lowRectangle1_91 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨92,_⟩ => convert lowRectangle1_92 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨93,_⟩ => convert lowRectangle1_93 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨94,_⟩ => convert lowRectangle1_94 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨95,_⟩ => convert lowRectangle1_95 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨96,_⟩ => convert lowRectangle1_96 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨97,_⟩ => convert lowRectangle1_97 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨98,_⟩ => convert lowRectangle1_98 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨99,_⟩ => convert lowRectangle1_99 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨100,_⟩ => convert lowRectangle1_100 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨101,_⟩ => convert lowRectangle1_101 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨102,_⟩ => convert lowRectangle1_102 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨103,_⟩ => convert lowRectangle1_103 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨104,_⟩ => convert lowRectangle1_104 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨105,_⟩ => convert lowRectangle1_105 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨106,_⟩ => convert lowRectangle1_106 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨107,_⟩ => convert lowRectangle1_107 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨108,_⟩ => convert lowRectangle1_108 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨109,_⟩ => convert lowRectangle1_109 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨110,_⟩ => convert lowRectangle1_110 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨111,_⟩ => convert lowRectangle1_111 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨112,_⟩ => convert lowRectangle1_112 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨113,_⟩ => convert lowRectangle1_113 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨114,_⟩ => convert lowRectangle1_114 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨115,_⟩ => convert lowRectangle1_115 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨116,_⟩ => convert lowRectangle1_116 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨117,_⟩ => convert lowRectangle1_117 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨118,_⟩ => convert lowRectangle1_118 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨119,_⟩ => convert lowRectangle1_119 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨120,_⟩ => convert lowRectangle1_120 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨121,_⟩ => convert lowRectangle1_121 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨122,_⟩ => convert lowRectangle1_122 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨123,_⟩ => convert lowRectangle1_123 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨124,_⟩ => convert lowRectangle1_124 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨125,_⟩ => convert lowRectangle1_125 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨126,_⟩ => convert lowRectangle1_126 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨127,_⟩ => convert lowRectangle1_127 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨128,_⟩ => convert lowRectangle1_128 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨129,_⟩ => convert lowRectangle1_129 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨130,_⟩ => convert lowRectangle1_130 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨131,_⟩ => convert lowRectangle1_131 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨132,_⟩ => convert lowRectangle1_132 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨133,_⟩ => convert lowRectangle1_133 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨134,_⟩ => convert lowRectangle1_134 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨135,_⟩ => convert lowRectangle1_135 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨136,_⟩ => convert lowRectangle1_136 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨137,_⟩ => convert lowRectangle1_137 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨138,_⟩ => convert lowRectangle1_138 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨139,_⟩ => convert lowRectangle1_139 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨140,_⟩ => convert lowRectangle1_140 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨141,_⟩ => convert lowRectangle1_141 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨142,_⟩ => convert lowRectangle1_142 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨143,_⟩ => convert lowRectangle1_143 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨144,_⟩ => convert lowRectangle1_144 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨145,_⟩ => convert lowRectangle1_145 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨146,_⟩ => convert lowRectangle1_146 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨147,_⟩ => convert lowRectangle1_147 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨148,_⟩ => convert lowRectangle1_148 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨149,_⟩ => convert lowRectangle1_149 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨150,_⟩ => convert lowRectangle1_150 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨151,_⟩ => convert lowRectangle1_151 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨152,_⟩ => convert lowRectangle1_152 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨153,_⟩ => convert lowRectangle1_153 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨154,_⟩ => convert lowRectangle1_154 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨155,_⟩ => convert lowRectangle1_155 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨156,_⟩ => convert lowRectangle1_156 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨157,_⟩ => convert lowRectangle1_157 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨158,_⟩ => convert lowRectangle1_158 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨159,_⟩ => convert lowRectangle1_159 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨j+160,h⟩ => exact False.elim (by omega)
end BstLean.BlueprintLow
