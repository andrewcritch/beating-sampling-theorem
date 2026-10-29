import BstLean.Part291Rectangle
import BstLean.Part291Certificates2
import BstLean.Part291LocalEnergyBatch0
import BstLean.Part291LocalEnergyBatch1
namespace BstLean.BlueprintLow
open Real Set BstLean.Part255
noncomputable def lowRectangle2_0 : FrameRectangleCertificate 8500 9000 (23/50) (921/2000) lowTIParameters0 where
  full := (104994086277/1000000000000)
  energy := (44267434443/62500000000)
  cov := (142244632117/500000000000)
  schur := (65584707479/62500000000)
  cap := (936447431/1000000000000)
  W2 := (3671129537579/1000000000000)
  V := (281311267/1000000000000)
  mass := (154541363/1000000000000)
  rootN := (1024380456503/1000000000000)
  rootB := (15300714289/500000000000)
  rootU := (310421846607/500000000000)
  rootV := (16772336361/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_0.scalar_checked
  centre := fun n hn => lowFull2_0 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy0 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_0.bound (by norm_num) hn lowTIParameters0_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_1 : FrameRectangleCertificate 8500 9000 (921/2000) (461/1000) lowTIParameters1 where
  full := (105074129883/1000000000000)
  energy := (708032000171/1000000000000)
  cov := (71167890993/250000000000)
  schur := (1049079290111/1000000000000)
  cap := (937022107/1000000000000)
  W2 := (1833890849873/500000000000)
  V := (281491531/1000000000000)
  mass := (36042843/250000000000)
  rootN := (256061429411/250000000000)
  rootB := (30610816831/1000000000000)
  rootU := (124159408939/200000000000)
  rootV := (335554187/20000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_1.scalar_checked
  centre := fun n hn => lowFull2_1 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy1 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_1.bound (by norm_num) hn lowTIParameters1_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_2 : FrameRectangleCertificate 8500 9000 (461/1000) (923/2000) lowTIParameters2 where
  full := (105154262929/1000000000000)
  energy := (353892583027/500000000000)
  cov := (71213418961/250000000000)
  schur := (524401765231/500000000000)
  cap := (937596531/1000000000000)
  W2 := (458055191679/125000000000)
  V := (35208951/125000000000)
  mass := (33699619/250000000000)
  rootN := (1024111092833/1000000000000)
  rootB := (30620198089/1000000000000)
  rootU := (77593859343/125000000000)
  rootV := (16783075047/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_2.scalar_checked
  centre := fun n hn => lowFull2_2 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy2 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_2.bound (by norm_num) hn lowTIParameters2_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_3 : FrameRectangleCertificate 8500 9000 (923/2000) (231/500) lowTIParameters3 where
  full := (52617243401/500000000000)
  energy := (707538448651/1000000000000)
  cov := (285161583007/1000000000000)
  schur := (1048991167027/1000000000000)
  cap := (469223319/500000000000)
  W2 := (14301207079/3906250000)
  V := (70494019/250000000000)
  mass := (126323117/1000000000000)
  rootN := (512101349107/500000000000)
  rootB := (30634076419/1000000000000)
  rootU := (620705186081/1000000000000)
  rootV := (8396071641/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_3.scalar_checked
  centre := fun n hn => lowFull2_3 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy3 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_3.bound (by norm_num) hn lowTIParameters3_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_4 : FrameRectangleCertificate 8500 9000 (231/500) (37/80) lowTIParameters4 where
  full := (105314802903/1000000000000)
  energy := (707291847877/1000000000000)
  cov := (285217335249/1000000000000)
  schur := (104825281237/100000000000)
  cap := (187748929/200000000000)
  W2 := (457223013737/125000000000)
  V := (56406241/200000000000)
  mass := (29664011/250000000000)
  rootN := (1023842181379/1000000000000)
  rootB := (7659735003/250000000000)
  rootU := (155164995367/250000000000)
  rootV := (8396892357/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_4.scalar_checked
  centre := fun n hn => lowFull2_4 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy4 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_4.bound (by norm_num) hn lowTIParameters4_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_5 : FrameRectangleCertificate 8500 9000 (37/80) (463/1000) lowTIParameters5 where
  full := (26348803163/250000000000)
  energy := (176761340913/250000000000)
  cov := (71381242547/250000000000)
  schur := (1048440526867/1000000000000)
  cap := (46979723/50000000000)
  W2 := (1827233400193/500000000000)
  V := (282335403/1000000000000)
  mass := (27929301/250000000000)
  rootN := (1023933848873/1000000000000)
  rootB := (7663201273/250000000000)
  rootU := (155153815929/250000000000)
  rootV := (525088723/31250000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_5.scalar_checked
  centre := fun n hn => lowFull2_5 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy5 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_5.bound (by norm_num) hn lowTIParameters5_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_6 : FrameRectangleCertificate 8500 9000 (463/1000) (927/2000) lowTIParameters6 where
  full := (26368929371/250000000000)
  energy := (44174937243/62500000000)
  cov := (8924382659/31250000000)
  schur := (261925790917/250000000000)
  cap := (939891799/1000000000000)
  W2 := (1825578528831/500000000000)
  V := (282390061/1000000000000)
  mass := (21086953/200000000000)
  rootN := (511786860829/500000000000)
  rootB := (30657654819/1000000000000)
  rootU := (620571035663/1000000000000)
  rootV := (4201116377/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_6.scalar_checked
  centre := fun n hn => lowFull2_6 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy6 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_6.bound (by norm_num) hn lowTIParameters6_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_7 : FrameRectangleCertificate 8500 9000 (927/2000) (58/125) lowTIParameters7 where
  full := (2111126377/20000000000)
  energy := (141310548901/200000000000)
  cov := (285887608169/1000000000000)
  schur := (1047890954207/1000000000000)
  cap := (470370669/500000000000)
  W2 := (29182838847/8000000000)
  V := (28269399/100000000000)
  mass := (1246803/12500000000)
  rootN := (511832725167/500000000000)
  rootB := (30671506941/1000000000000)
  rootU := (310263650097/500000000000)
  rootV := (16813506179/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_7.scalar_checked
  centre := fun n hn => lowFull2_7 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy7 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_7.bound (by norm_num) hn lowTIParameters7_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_8 : FrameRectangleCertificate 8500 9000 (58/125) (929/2000) lowTIParameters8 where
  full := (5281850911/50000000000)
  energy := (35315330471/50000000000)
  cov := (71485601429/250000000000)
  schur := (1047154574337/1000000000000)
  cap := (941038021/1000000000000)
  W2 := (3644560169339/1000000000000)
  V := (17671761/62500000000)
  mass := (9458771/100000000000)
  rootN := (102330570913/100000000000)
  rootB := (30676343019/1000000000000)
  rootU := (620484060241/1000000000000)
  rootV := (4203779371/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_8.scalar_checked
  centre := fun n hn => lowFull2_8 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy8 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_8.bound (by norm_num) hn lowTIParameters8_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_9 : FrameRectangleCertificate 8500 9000 (929/2000) (93/200) lowTIParameters9 where
  full := (105717817079/1000000000000)
  energy := (353030295273/500000000000)
  cov := (143124748649/500000000000)
  schur := (523671219527/500000000000)
  cap := (470943649/500000000000)
  W2 := (364127297233/100000000000)
  V := (283051837/1000000000000)
  mass := (8991313/100000000000)
  rootN := (102339749807/100000000000)
  rootB := (30690182437/1000000000000)
  rootU := (15511032969/25000000000)
  rootV := (8412072233/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_9.scalar_checked
  centre := fun n hn => lowFull2_9 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy9 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_9.bound (by norm_num) hn lowTIParameters9_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_10 : FrameRectangleCertificate 8500 9000 (93/200) (931/2000) lowTIParameters10 where
  full := (105798716931/1000000000000)
  energy := (705814687803/1000000000000)
  cov := (143151908959/500000000000)
  schur := (261651758999/250000000000)
  cap := (471091671/500000000000)
  W2 := (363799323937/100000000000)
  V := (283105551/1000000000000)
  mass := (42836859/500000000000)
  rootN := (20460762801/20000000000)
  rootB := (7673751291/250000000000)
  rootU := (620399078763/1000000000000)
  rootV := (16825740727/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_10.scalar_checked
  centre := fun n hn => lowFull2_10 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy10 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_10.bound (by norm_num) hn lowTIParameters10_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_11 : FrameRectangleCertificate 8500 9000 (931/2000) (233/500) lowTIParameters11 where
  full := (827185307/7812500000)
  energy := (705568901107/1000000000000)
  cov := (71652659591/250000000000)
  schur := (1046794973059/1000000000000)
  cap := (943032369/1000000000000)
  W2 := (36347209451/10000000000)
  V := (17713059/62500000000)
  mass := (20456849/250000000000)
  rootN := (1023129988349/1000000000000)
  rootB := (30708832101/1000000000000)
  rootU := (620357343301/1000000000000)
  rootV := (16834754053/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_11.scalar_checked
  centre := fun n hn => lowFull2_11 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy11 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_11.bound (by norm_num) hn lowTIParameters11_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_12 : FrameRectangleCertificate 8500 9000 (233/500) (933/2000) lowTIParameters12 where
  full := (52980412857/500000000000)
  energy := (88165403797/125000000000)
  cov := (286664482949/1000000000000)
  schur := (523030271053/500000000000)
  cap := (471663893/500000000000)
  W2 := (453932008023/125000000000)
  V := (283462187/1000000000000)
  mass := (39168153/500000000000)
  rootN := (102277101157/100000000000)
  rootB := (30713641693/1000000000000)
  rootU := (124063223093/200000000000)
  rootV := (420908383/25000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_12.scalar_checked
  centre := fun n hn => lowFull2_12 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy12 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_12.bound (by norm_num) hn lowTIParameters12_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_13 : FrameRectangleCertificate 8500 9000 (933/2000) (467/1000) lowTIParameters13 where
  full := (106042037739/1000000000000)
  energy := (352538837763/500000000000)
  cov := (286971032619/1000000000000)
  schur := (209249709937/200000000000)
  cap := (47208829/50000000000)
  W2 := (3628198571491/1000000000000)
  V := (4433833/15625000000)
  mass := (18791593/250000000000)
  rootN := (511431459163/500000000000)
  rootB := (7681864113/250000000000)
  rootU := (310137699193/500000000000)
  rootV := (8422667511/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_13.scalar_checked
  centre := fun n hn => lowFull2_13 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy13 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_13.bound (by norm_num) hn lowTIParameters13_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_14 : FrameRectangleCertificate 8500 9000 (467/1000) (187/400) lowTIParameters14 where
  full := (106123356947/1000000000000)
  energy := (704832236477/1000000000000)
  cov := (287024402033/1000000000000)
  schur := (522757543027/500000000000)
  cap := (94447139/100000000000)
  W2 := (3624948441999/1000000000000)
  V := (56763617/200000000000)
  mass := (14457381/200000000000)
  rootN := (1278130401/1250000000)
  rootB := (30732253253/1000000000000)
  rootU := (620235195249/1000000000000)
  rootV := (4211725337/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_14.scalar_checked
  centre := fun n hn => lowFull2_14 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy14 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_14.bound (by norm_num) hn lowTIParameters14_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_15 : FrameRectangleCertificate 8500 9000 (187/400) (117/250) lowTIParameters15 where
  full := (53102392463/500000000000)
  energy := (88073364143/125000000000)
  cov := (35916335161/125000000000)
  schur := (1045703162357/1000000000000)
  cap := (945319963/1000000000000)
  W2 := (724341130143/200000000000)
  V := (284120943/1000000000000)
  mass := (69670257/1000000000000)
  rootN := (127824535641/125000000000)
  rootB := (30746056057/1000000000000)
  rootU := (124039101851/200000000000)
  rootV := (131686621/7812500000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_15.scalar_checked
  centre := fun n hn => lowFull2_15 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy15 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_15.bound (by norm_num) hn lowTIParameters15_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_16 : FrameRectangleCertificate 8500 9000 (117/250) (937/2000) lowTIParameters16 where
  full := (106286323289/1000000000000)
  energy := (140868341089/200000000000)
  cov := (287383575947/1000000000000)
  schur := (41798826387/40000000000)
  cap := (472807089/500000000000)
  W2 := (1809235086411/500000000000)
  V := (284173247/1000000000000)
  mass := (67291511/1000000000000)
  rootN := (1022238064091/1000000000000)
  rootB := (15375420141/500000000000)
  rootU := (24806253747/40000000000)
  rootV := (8428719461/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_16.scalar_checked
  centre := fun n hn => lowFull2_16 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy16 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_16.bound (by norm_num) hn lowTIParameters16_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_17 : FrameRectangleCertificate 8500 9000 (937/2000) (469/1000) lowTIParameters17 where
  full := (53183986831/500000000000)
  energy := (704096613301/1000000000000)
  cov := (35961198143/125000000000)
  schur := (1045158802931/1000000000000)
  cap := (946462547/1000000000000)
  W2 := (1807620991829/500000000000)
  V := (142237919/500000000000)
  mass := (16282049/250000000000)
  rootN := (204466017023/200000000000)
  rootB := (3076463143/100000000000)
  rootU := (155029425453/250000000000)
  rootV := (16866411533/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_17.scalar_checked
  centre := fun n hn => lowFull2_17 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy17 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_17.bound (by norm_num) hn lowTIParameters17_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_18 : FrameRectangleCertificate 8500 9000 (469/1000) (939/2000) lowTIParameters18 where
  full := (53224868847/500000000000)
  energy := (703851636627/1000000000000)
  cov := (2877420059/10000000000)
  schur := (261106814117/250000000000)
  cap := (189351237/200000000000)
  W2 := (1806010529281/500000000000)
  V := (284527673/1000000000000)
  mass := (31580023/500000000000)
  rootN := (5109861193/5000000000)
  rootB := (30769403391/1000000000000)
  rootU := (620079587013/1000000000000)
  rootV := (16867948097/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_18.scalar_checked
  centre := fun n hn => lowFull2_18 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy18 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_18.bound (by norm_num) hn lowTIParameters18_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_19 : FrameRectangleCertificate 8500 9000 (939/2000) (47/100) lowTIParameters19 where
  full := (13316452131/125000000000)
  energy := (351803387671/500000000000)
  cov := (144023872697/500000000000)
  schur := (130576933113/125000000000)
  cap := (189520873/200000000000)
  W2 := (902201843279/250000000000)
  V := (284829997/1000000000000)
  mass := (6136877/100000000000)
  rootN := (255516078861/250000000000)
  rootB := (30783183153/1000000000000)
  rootU := (620042002669/1000000000000)
  rootV := (16876907211/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_19.scalar_checked
  centre := fun n hn => lowFull2_19 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy19 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_19.bound (by norm_num) hn lowTIParameters19_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_20 : FrameRectangleCertificate 8500 9000 (47/100) (941/2000) lowTIParameters20 where
  full := (106613613409/1000000000000)
  energy := (703362029363/1000000000000)
  cov := (1800623079/6250000000)
  schur := (1043884868323/1000000000000)
  cap := (947897439/1000000000000)
  W2 := (450700112857/125000000000)
  V := (71220341/250000000000)
  mass := (59737853/1000000000000)
  rootN := (127713355087/125000000000)
  rootB := (30787943079/1000000000000)
  rootU := (62000495221/100000000000)
  rootV := (4219607239/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_20.scalar_checked
  centre := fun n hn => lowFull2_20 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy20 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_20.bound (by norm_num) hn lowTIParameters20_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_21 : FrameRectangleCertificate 8500 9000 (941/2000) (471/1000) lowTIParameters21 where
  full := (106695728479/1000000000000)
  energy := (175779349653/250000000000)
  cov := (288405162789/1000000000000)
  schur := (261018285053/250000000000)
  cap := (474372723/500000000000)
  W2 := (1801200811813/500000000000)
  V := (142591711/500000000000)
  mass := (29126191/500000000000)
  rootN := (204359794501/200000000000)
  rootB := (30801711739/1000000000000)
  rootU := (309984219561/500000000000)
  rootV := (8443687317/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_21.scalar_checked
  centre := fun n hn => lowFull2_21 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy21 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_21.bound (by norm_num) hn lowTIParameters21_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_22 : FrameRectangleCertificate 8500 9000 (471/1000) (943/2000) lowTIParameters22 where
  full := (5338898199/50000000000)
  energy := (702872883003/1000000000000)
  cov := (288710633201/1000000000000)
  schur := (1044261526477/1000000000000)
  cap := (474796821/500000000000)
  W2 := (1799604755579/500000000000)
  V := (7137137/25000000000)
  mass := (56898881/1000000000000)
  rootN := (255472787993/250000000000)
  rootB := (30815477313/1000000000000)
  rootU := (309966233459/500000000000)
  rootV := (675852623/40000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_22.scalar_checked
  centre := fun n hn => lowFull2_22 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy22 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_22.bound (by norm_num) hn lowTIParameters22_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_23 : FrameRectangleCertificate 8500 9000 (943/2000) (59/125) lowTIParameters23 where
  full := (53430160827/500000000000)
  energy := (702628482457/1000000000000)
  cov := (2312128831/8000000000)
  schur := (261112506683/250000000000)
  cap := (950442033/1000000000000)
  W2 := (719204908289/200000000000)
  V := (142893769/500000000000)
  mass := (55665169/1000000000000)
  rootN := (1021983378893/1000000000000)
  rootB := (963413747/31250000000)
  rootU := (619897039173/1000000000000)
  rootV := (4226312947/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_23.scalar_checked
  centre := fun n hn => lowFull2_23 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy23 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_23.bound (by norm_num) hn lowTIParameters23_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_24 : FrameRectangleCertificate 8500 9000 (59/125) (189/400) lowTIParameters24 where
  full := (53471401631/500000000000)
  energy := (140476839379/200000000000)
  cov := (289321574807/1000000000000)
  schur := (1044638640611/1000000000000)
  cap := (951290621/1000000000000)
  W2 := (224552918163/62500000000)
  V := (286089597/1000000000000)
  mass := (54540231/1000000000000)
  rootN := (1022075653077/1000000000000)
  rootB := (30842999547/1000000000000)
  rootU := (38741384969/62500000000)
  rootV := (16914183309/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_24.scalar_checked
  centre := fun n hn => lowFull2_24 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy24 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_24.bound (by norm_num) hn lowTIParameters24_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_25 : FrameRectangleCertificate 8500 9000 (189/400) (473/1000) lowTIParameters25 where
  full := (53512705291/500000000000)
  energy := (351070013117/500000000000)
  cov := (144813523001/500000000000)
  schur := (1044827367731/1000000000000)
  cap := (95213941/100000000000)
  W2 := (717935186949/200000000000)
  V := (57278331/200000000000)
  mass := (53514103/1000000000000)
  rootN := (1022167974323/1000000000000)
  rootB := (30856756311/1000000000000)
  rootU := (619827831557/1000000000000)
  rootV := (16923110087/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_25.scalar_checked
  centre := fun n hn => lowFull2_25 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy25 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_25.bound (by norm_num) hn lowTIParameters25_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_26 : FrameRectangleCertificate 8500 9000 (473/1000) (947/2000) lowTIParameters26 where
  full := (13388518177/125000000000)
  energy := (350947985197/500000000000)
  cov := (289932517457/1000000000000)
  schur := (522508103861/500000000000)
  cap := (119123551/125000000000)
  W2 := (3586512250167/1000000000000)
  V := (57338743/200000000000)
  mass := (52577767/1000000000000)
  rootN := (1022260342439/1000000000000)
  rootB := (3087051033/100000000000)
  rootU := (123958811809/200000000000)
  rootV := (8466016109/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_26.scalar_checked
  centre := fun n hn => lowFull2_26 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy26 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_26.bound (by norm_num) hn lowTIParameters26_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_27 : FrameRectangleCertificate 8500 9000 (947/2000) (237/500) lowTIParameters27 where
  full := (107191009581/1000000000000)
  energy := (701652029291/1000000000000)
  cov := (145118994587/500000000000)
  schur := (1045205160201/1000000000000)
  cap := (953837611/1000000000000)
  W2 := (716671122641/200000000000)
  V := (143497887/500000000000)
  mass := (51723059/1000000000000)
  rootN := (1022352757223/1000000000000)
  rootB := (30884261543/1000000000000)
  rootU := (77470105713/125000000000)
  rootV := (847047481/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_27.scalar_checked
  centre := fun n hn => lowFull2_27 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy27 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_27.bound (by norm_num) hn lowTIParameters27_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_28 : FrameRectangleCertificate 8500 9000 (237/500) (949/2000) lowTIParameters28 where
  full := (2681850123/25000000000)
  energy := (701408202847/1000000000000)
  cov := (290543461147/1000000000000)
  schur := (52269711239/50000000000)
  cap := (954687031/1000000000000)
  W2 := (3580206000359/1000000000000)
  V := (287297833/1000000000000)
  mass := (6367823/125000000000)
  rootN := (511222609237/500000000000)
  rootB := (30898010147/1000000000000)
  rootU := (619728195339/1000000000000)
  rootV := (1694986233/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_28.scalar_checked
  centre := fun n hn => lowFull2_28 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy28 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_28.bound (by norm_num) hn lowTIParameters28_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_29 : FrameRectangleCertificate 8500 9000 (949/2000) (19/40) lowTIParameters29 where
  full := (107357133291/1000000000000)
  energy := (87645561373/125000000000)
  cov := (145424466691/500000000000)
  schur := (1045583401131/1000000000000)
  cap := (238884167/250000000000)
  W2 := (3577063388297/1000000000000)
  V := (287599893/1000000000000)
  mass := (50229643/1000000000000)
  rootN := (1022537726019/1000000000000)
  rootB := (15455878073/500000000000)
  rootU := (619696111791/1000000000000)
  rootV := (8479385193/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_29.scalar_checked
  centre := fun n hn => lowFull2_29 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy29 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_29.bound (by norm_num) hn lowTIParameters29_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_30 : FrameRectangleCertificate 8500 9000 (19/40) (951/2000) lowTIParameters30 where
  full := (53720198287/500000000000)
  energy := (350460446809/500000000000)
  cov := (72788601469/250000000000)
  schur := (522886344429/500000000000)
  cap := (38255461/40000000000)
  W2 := (89348193841/25000000000)
  V := (287901953/1000000000000)
  mass := (12394541/250000000000)
  rootN := (1022630279651/1000000000000)
  rootB := (3865687449/125000000000)
  rootU := (619664598939/1000000000000)
  rootV := (8483836883/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_30.scalar_checked
  centre := fun n hn => lowFull2_30 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy30 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_30.bound (by norm_num) hn lowTIParameters30_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_31 : FrameRectangleCertificate 8500 9000 (951/2000) (119/250) lowTIParameters31 where
  full := (107523796671/1000000000000)
  energy := (700677410671/1000000000000)
  cov := (291459878627/1000000000000)
  schur := (1045962087597/1000000000000)
  cap := (957236609/1000000000000)
  W2 := (3570799073241/1000000000000)
  V := (144102007/500000000000)
  mass := (48982641/1000000000000)
  rootN := (51136143959/50000000000)
  rootB := (15469620301/500000000000)
  rootU := (309816830363/500000000000)
  rootV := (3395314501/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_31.scalar_checked
  centre := fun n hn => lowFull2_31 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy31 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_31.bound (by norm_num) hn lowTIParameters31_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_32 : FrameRectangleCertificate 8500 9000 (119/250) (953/2000) lowTIParameters32 where
  full := (107607335503/1000000000000)
  energy := (350217021031/500000000000)
  cov := (58353070327/200000000000)
  schur := (1046151596979/1000000000000)
  cap := (239521731/250000000000)
  W2 := (891919330987/250000000000)
  V := (144253037/500000000000)
  mass := (48438079/1000000000000)
  rootN := (1022815524413/1000000000000)
  rootB := (30952979243/1000000000000)
  rootU := (4956826409/8000000000)
  rootV := (16985466553/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_32.scalar_checked
  centre := fun n hn => lowFull2_32 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy32 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_32.bound (by norm_num) hn lowTIParameters32_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_33 : FrameRectangleCertificate 8500 9000 (953/2000) (477/1000) lowTIParameters33 where
  full := (26922753753/250000000000)
  energy := (700190787709/1000000000000)
  cov := (146035412451/500000000000)
  schur := (1046341216643/1000000000000)
  cap := (7491699/7812500000)
  W2 := (445570310347/125000000000)
  V := (57761627/200000000000)
  mass := (47939947/1000000000000)
  rootN := (1022908215161/1000000000000)
  rootB := (30966715551/1000000000000)
  rootU := (154893381041/250000000000)
  rootV := (679774239/40000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_33.scalar_checked
  centre := fun n hn => lowFull2_33 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy33 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_33.bound (by norm_num) hn lowTIParameters33_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_34 : FrameRectangleCertificate 8500 9000 (477/1000) (191/400) lowTIParameters34 where
  full := (107774837161/1000000000000)
  energy := (349973823769/500000000000)
  cov := (292376298423/1000000000000)
  schur := (523265473113/500000000000)
  cap := (959788259/1000000000000)
  W2 := (22259090793/6250000000)
  V := (72277549/250000000000)
  mass := (47484131/1000000000000)
  rootN := (204600190247/200000000000)
  rootB := (15490224813/500000000000)
  rootU := (619544333919/1000000000000)
  rootV := (68012963/4000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_34.scalar_checked
  centre := fun n hn => lowFull2_34 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy34 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_34.bound (by norm_num) hn lowTIParameters34_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_35 : FrameRectangleCertificate 8500 9000 (191/400) (239/500) lowTIParameters35 where
  full := (21571760787/200000000000)
  energy := (349852310731/500000000000)
  cov := (58536354441/200000000000)
  schur := (523360392689/500000000000)
  cap := (96063929/100000000000)
  W2 := (1779176716707/500000000000)
  V := (144706129/500000000000)
  mass := (9413379/200000000000)
  rootN := (20461874649/20000000000)
  rootB := (30994181551/1000000000000)
  rootU := (619515734511/1000000000000)
  rootV := (3402424183/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_35.scalar_checked
  centre := fun n hn => lowFull2_35 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy35 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_35.bound (by norm_num) hn lowTIParameters35_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_36 : FrameRectangleCertificate 8500 9000 (239/500) (957/2000) lowTIParameters36 where
  full := (107942917341/1000000000000)
  energy := (699461709407/1000000000000)
  cov := (292987246241/1000000000000)
  schur := (1046910733737/1000000000000)
  cap := (961490569/1000000000000)
  W2 := (444407397467/125000000000)
  V := (289714319/1000000000000)
  mass := (11671211/250000000000)
  rootN := (1023186558619/1000000000000)
  rootB := (15503955697/500000000000)
  rootU := (154871932529/250000000000)
  rootV := (17020996417/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_36.scalar_checked
  centre := fun n hn => lowFull2_36 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy36 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_36.bound (by norm_num) hn lowTIParameters36_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_37 : FrameRectangleCertificate 8500 9000 (957/2000) (479/1000) lowTIParameters37 where
  full := (27006794851/250000000000)
  energy := (699218911291/1000000000000)
  cov := (293292720529/1000000000000)
  schur := (523550395463/500000000000)
  cap := (962342099/1000000000000)
  W2 := (3552171743239/1000000000000)
  V := (290016381/1000000000000)
  mass := (46334897/1000000000000)
  rootN := (127909928693/125000000000)
  rootB := (15510819603/500000000000)
  rootU := (123892064989/200000000000)
  rootV := (8514933661/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_37.scalar_checked
  centre := fun n hn => lowFull2_37 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy37 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_37.bound (by norm_num) hn lowTIParameters37_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_38 : FrameRectangleCertificate 8500 9000 (479/1000) (959/2000) lowTIParameters38 where
  full := (6756974511/62500000000)
  energy := (349488113519/500000000000)
  cov := (293598195077/1000000000000)
  schur := (261822739159/250000000000)
  cap := (240798471/250000000000)
  W2 := (3549091101479/1000000000000)
  V := (290318443/1000000000000)
  mass := (5751781/125000000000)
  rootN := (511686172531/500000000000)
  rootB := (15517682527/500000000000)
  rootU := (619433523277/1000000000000)
  rootV := (1703873361/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_38.scalar_checked
  centre := fun n hn => lowFull2_38 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy38 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_38.bound (by norm_num) hn lowTIParameters38_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_39 : FrameRectangleCertificate 8500 9000 (959/2000) (12/25) lowTIParameters39 where
  full := (4327846309/40000000000)
  energy := (139746731313/200000000000)
  cov := (146951834939/500000000000)
  schur := (1047481230477/1000000000000)
  cap := (96404593/100000000000)
  W2 := (709203446401/200000000000)
  V := (145310253/500000000000)
  mass := (45720349/1000000000000)
  rootN := (102346530497/100000000000)
  rootB := (31049089037/1000000000000)
  rootU := (619407329413/1000000000000)
  rootV := (3409519063/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_39.scalar_checked
  centre := fun n hn => lowFull2_39 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy39 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_39.bound (by norm_num) hn lowTIParameters39_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_40 : FrameRectangleCertificate 8500 9000 (12/25) (961/2000) lowTIParameters40 where
  full := (54140439073/500000000000)
  energy := (698491199793/1000000000000)
  cov := (58327182829/200000000000)
  schur := (207703064931/200000000000)
  cap := (959276123/1000000000000)
  W2 := (3542950112527/1000000000000)
  V := (288378083/1000000000000)
  mass := (71017/1562500000)
  rootN := (1019075720767/1000000000000)
  rootB := (7743045763/250000000000)
  rootU := (619381747723/1000000000000)
  rootV := (16981698473/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_40.scalar_checked
  centre := fun n hn => lowFull2_40 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy40 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_40.bound (by norm_num) hn lowTIParameters40_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_41 : FrameRectangleCertificate 8500 9000 (961/2000) (481/1000) lowTIParameters41 where
  full := (108365755553/1000000000000)
  energy := (698248856647/1000000000000)
  cov := (2335509681/8000000000)
  schur := (519352069799/500000000000)
  cap := (192024667/200000000000)
  W2 := (707977944179/200000000000)
  V := (36084687/125000000000)
  mass := (4520373/100000000000)
  rootN := (1019168356847/1000000000000)
  rootB := (3873232127/125000000000)
  rootU := (309678391311/500000000000)
  rootV := (16990511941/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_41.scalar_checked
  centre := fun n hn => lowFull2_41 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy41 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_41.bound (by norm_num) hn lowTIParameters41_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_42 : FrameRectangleCertificate 8500 9000 (481/1000) (963/2000) lowTIParameters42 where
  full := (21690158417/200000000000)
  energy := (349003313523/500000000000)
  cov := (292241506357/1000000000000)
  schur := (129861632589/125000000000)
  cap := (120121353/125000000000)
  W2 := (3536836035033/1000000000000)
  V := (28897691/100000000000)
  mass := (22488489/500000000000)
  rootN := (1019261036591/1000000000000)
  rootB := (3874941177/125000000000)
  rootU := (309666219289/500000000000)
  rootV := (16999320869/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_42.scalar_checked
  centre := fun n hn => lowFull2_42 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy42 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_42.bound (by norm_num) hn lowTIParameters42_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_43 : FrameRectangleCertificate 8500 9000 (963/2000) (241/500) lowTIParameters43 where
  full := (108535989901/1000000000000)
  energy := (697764510909/1000000000000)
  cov := (73136075709/250000000000)
  schur := (1039082087607/1000000000000)
  cap := (961818593/1000000000000)
  W2 := (3533789032857/1000000000000)
  V := (72319081/250000000000)
  mass := (44768873/1000000000000)
  rootN := (203870751959/200000000000)
  rootB := (31013200303/1000000000000)
  rootU := (619308720093/1000000000000)
  rootV := (3401625047/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_43.scalar_checked
  centre := fun n hn => lowFull2_43 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy43 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_43.bound (by norm_num) hn lowTIParameters43_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_44 : FrameRectangleCertificate 8500 9000 (241/500) (193/400) lowTIParameters44 where
  full := (54310675591/500000000000)
  energy := (348761254081/500000000000)
  cov := (292847099569/1000000000000)
  schur := (51963561/50000000)
  cap := (481333323/500000000000)
  W2 := (3530748692569/1000000000000)
  V := (144787869/500000000000)
  mass := (44577823/1000000000000)
  rootN := (254861631577/250000000000)
  rootB := (31026869743/1000000000000)
  rootU := (619285631733/1000000000000)
  rootV := (8508462523/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_44.scalar_checked
  centre := fun n hn => lowFull2_44 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy44 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_44.bound (by norm_num) hn lowTIParameters44_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_45 : FrameRectangleCertificate 8500 9000 (193/400) (483/1000) lowTIParameters45 where
  full := (108706878137/1000000000000)
  energy := (174320154681/250000000000)
  cov := (5862997931/20000000000)
  schur := (259865114379/250000000000)
  cap := (963514987/1000000000000)
  W2 := (3527714992317/1000000000000)
  V := (289875153/1000000000000)
  mass := (22201187/500000000000)
  rootN := (509769667967/500000000000)
  rootB := (15520268901/500000000000)
  rootU := (309631589059/500000000000)
  rootV := (8512860169/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_45.scalar_checked
  centre := fun n hn => lowFull2_45 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy45 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_45.bound (by norm_num) hn lowTIParameters45_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_46 : FrameRectangleCertificate 8500 9000 (483/1000) (967/2000) lowTIParameters46 where
  full := (54396286497/500000000000)
  energy := (348519421259/500000000000)
  cov := (293452693781/1000000000000)
  schur := (129956224979/125000000000)
  cap := (7714909/8000000000)
  W2 := (881171977607/250000000000)
  V := (290174567/1000000000000)
  mass := (22120601/500000000000)
  rootN := (127454023563/125000000000)
  rootB := (31054204627/1000000000000)
  rootU := (61924136391/100000000000)
  rootV := (17034511059/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_46.scalar_checked
  centre := fun n hn => lowFull2_46 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy46 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_46.bound (by norm_num) hn lowTIParameters46_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_47 : FrameRectangleCertificate 8500 9000 (967/2000) (121/250) lowTIParameters47 where
  full := (108878438003/1000000000000)
  energy := (87099647433/125000000000)
  cov := (14687774563/50000000000)
  schur := (259959811647/250000000000)
  cap := (482606281/500000000000)
  W2 := (3521667425219/1000000000000)
  V := (145236991/500000000000)
  mass := (44093099/1000000000000)
  rootN := (254931270957/250000000000)
  rootB := (31067870253/1000000000000)
  rootU := (154805048453/250000000000)
  rootV := (681731891/40000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_47.scalar_checked
  centre := fun n hn => lowFull2_47 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy47 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_47.bound (by norm_num) hn lowTIParameters47_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_48 : FrameRectangleCertificate 8500 9000 (121/250) (969/2000) lowTIParameters48 where
  full := (1362055943/12500000000)
  energy := (348277814743/500000000000)
  cov := (294058288987/1000000000000)
  schur := (520014398739/500000000000)
  cap := (966061803/1000000000000)
  W2 := (219915844703/62500000000)
  V := (145386699/500000000000)
  mass := (10989241/250000000000)
  rootN := (1019818021747/1000000000000)
  rootB := (777038369/25000000000)
  rootU := (619199672597/1000000000000)
  rootV := (8526039497/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_48.scalar_checked
  centre := fun n hn => lowFull2_48 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy48 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_48.bound (by norm_num) hn lowTIParameters48_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_49 : FrameRectangleCertificate 8500 9000 (969/2000) (97/200) lowTIParameters49 where
  full := (54525343803/500000000000)
  energy := (348157096253/500000000000)
  cov := (73590271741/250000000000)
  schur := (1040218452169/1000000000000)
  cap := (120863919/125000000000)
  W2 := (87891153977/25000000000)
  V := (291072813/1000000000000)
  mass := (4383179/100000000000)
  rootN := (1019911002083/1000000000000)
  rootB := (6219039643/200000000000)
  rootU := (619179805087/1000000000000)
  rootV := (17060856163/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_49.scalar_checked
  centre := fun n hn => lowFull2_49 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy49 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_49.bound (by norm_num) hn lowTIParameters49_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_50 : FrameRectangleCertificate 8500 9000 (97/200) (971/2000) lowTIParameters50 where
  full := (5456853841/50000000000)
  energy := (139214573689/200000000000)
  cov := (147331942593/500000000000)
  schur := (8128189143/7812500000)
  cap := (967761217/1000000000000)
  W2 := (3512645335353/1000000000000)
  V := (291372229/1000000000000)
  mass := (43716661/1000000000000)
  rootN := (1020004024651/1000000000000)
  rootB := (7777215187/250000000000)
  rootU := (123832119227/200000000000)
  rootV := (1066851803/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_50.scalar_checked
  centre := fun n hn => lowFull2_50 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy50 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_50.bound (by norm_num) hn lowTIParameters50_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_51 : FrameRectangleCertificate 8500 9000 (971/2000) (243/500) lowTIParameters51 where
  full := (13652955679/125000000000)
  energy := (695831657229/1000000000000)
  cov := (294966683657/1000000000000)
  schur := (208119614317/200000000000)
  cap := (968611401/1000000000000)
  W2 := (3509651022879/1000000000000)
  V := (58334329/200000000000)
  mass := (43610739/1000000000000)
  rootN := (510048544647/500000000000)
  rootB := (3890315301/125000000000)
  rootU := (24765682027/40000000000)
  rootV := (17078397027/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_51.scalar_checked
  centre := fun n hn => lowFull2_51 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy51 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_51.bound (by norm_num) hn lowTIParameters51_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_52 : FrameRectangleCertificate 8500 9000 (243/500) (973/2000) lowTIParameters52 where
  full := (109310395811/1000000000000)
  energy := (86948819847/125000000000)
  cov := (147634741187/500000000000)
  schur := (520394017829/500000000000)
  cap := (96946191/100000000000)
  W2 := (3506663200461/1000000000000)
  V := (291971061/1000000000000)
  mass := (21756629/500000000000)
  rootN := (510095097913/500000000000)
  rootB := (31136183293/1000000000000)
  rootU := (619124173667/1000000000000)
  rootV := (17087160707/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_52.scalar_checked
  centre := fun n hn => lowFull2_52 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy52 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_52.bound (by norm_num) hn lowTIParameters52_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_53 : FrameRectangleCertificate 8500 9000 (973/2000) (487/1000) lowTIParameters53 where
  full := (109397330353/1000000000000)
  energy := (69534957301/100000000000)
  cov := (147786140669/500000000000)
  schur := (104097810221/100000000000)
  cap := (970312747/1000000000000)
  W2 := (3503681847073/1000000000000)
  V := (292270477/1000000000000)
  mass := (43423519/1000000000000)
  rootN := (510141672041/500000000000)
  rootB := (31149843451/1000000000000)
  rootU := (619106970141/1000000000000)
  rootV := (8547959947/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_53.scalar_checked
  centre := fun n hn => lowFull2_53 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy53 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_53.bound (by norm_num) hn lowTIParameters53_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_54 : FrameRectangleCertificate 8500 9000 (487/1000) (39/80) lowTIParameters54 where
  full := (4379378059/40000000000)
  energy := (43444293741/62500000000)
  cov := (73968770137/250000000000)
  schur := (520584135461/500000000000)
  cap := (485581961/500000000000)
  W2 := (3500706941779/1000000000000)
  V := (146284947/500000000000)
  mass := (21670441/500000000000)
  rootN := (204075306779/200000000000)
  rootB := (6232700609/200000000000)
  rootU := (309545222583/500000000000)
  rootV := (136837397/8000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_54.scalar_checked
  centre := fun n hn => lowFull2_54 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy54 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_54.bound (by norm_num) hn lowTIParameters54_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_55 : FrameRectangleCertificate 8500 9000 (39/80) (61/125) lowTIParameters55 where
  full := (876574093/8000000000)
  energy := (694867939233/1000000000000)
  cov := (296177880003/1000000000000)
  schur := (20827170829/20000000000)
  cap := (486007717/500000000000)
  W2 := (3497738463653/1000000000000)
  V := (292869311/1000000000000)
  mass := (10816191/250000000000)
  rootN := (255117441271/250000000000)
  rootB := (31177162059/1000000000000)
  rootU := (309537301939/500000000000)
  rootV := (17113424877/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_55.scalar_checked
  centre := fun n hn => lowFull2_55 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy55 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_55.bound (by norm_num) hn lowTIParameters55_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_56 : FrameRectangleCertificate 8500 9000 (61/125) (977/2000) lowTIParameters56 where
  full := (109659263269/1000000000000)
  energy := (173656822767/250000000000)
  cov := (296480679703/1000000000000)
  schur := (65096807093/62500000000)
  cap := (972867293/1000000000000)
  W2 := (3494776391959/1000000000000)
  V := (36646091/125000000000)
  mass := (43194629/1000000000000)
  rootN := (1020563037489/1000000000000)
  rootB := (31190820653/1000000000000)
  rootU := (619059451453/1000000000000)
  rootV := (17122170657/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_56.scalar_checked
  centre := fun n hn => lowFull2_56 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy56 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_56.bound (by norm_num) hn lowTIParameters56_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_57 : FrameRectangleCertificate 8500 9000 (977/2000) (489/1000) lowTIParameters57 where
  full := (1097469589/10000000000)
  energy := (8679834441/12500000000)
  cov := (148391739823/500000000000)
  schur := (520869693349/500000000000)
  cap := (60857469/62500000000)
  W2 := (3491820705991/1000000000000)
  V := (58693629/200000000000)
  mass := (10782497/250000000000)
  rootN := (1020656350933/1000000000000)
  rootB := (3120447891/100000000000)
  rootU := (3869031207/6250000000)
  rootV := (17130911973/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_57.scalar_checked
  centre := fun n hn => lowFull2_57 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy57 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_57.bound (by norm_num) hn lowTIParameters57_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_58 : FrameRectangleCertificate 8500 9000 (489/1000) (979/2000) lowTIParameters58 where
  full := (109834851041/1000000000000)
  energy := (694146331799/1000000000000)
  cov := (297086279833/1000000000000)
  schur := (520964980397/500000000000)
  cap := (974572071/1000000000000)
  W2 := (872217846303/250000000000)
  V := (293767563/1000000000000)
  mass := (8614079/200000000000)
  rootN := (1020749705263/1000000000000)
  rootB := (7804534223/250000000000)
  rootU := (123806246837/200000000000)
  rootV := (17139648859/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_58.scalar_checked
  centre := fun n hn => lowFull2_58 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy58 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_58.bound (by norm_num) hn lowTIParameters58_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_59 : FrameRectangleCertificate 8500 9000 (979/2000) (49/100) lowTIParameters59 where
  full := (13740367779/125000000000)
  energy := (346953010271/500000000000)
  cov := (148694540133/500000000000)
  schur := (1042120635451/1000000000000)
  cap := (39017/40000000)
  W2 := (3485928409049/1000000000000)
  V := (294066981/1000000000000)
  mass := (21507719/500000000000)
  rootN := (1020843100311/1000000000000)
  rootB := (15615897349/500000000000)
  rootU := (61901817997/100000000000)
  rootV := (8574190647/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_59.scalar_checked
  centre := fun n hn => lowFull2_59 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy59 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_59.bound (by norm_num) hn lowTIParameters59_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_60 : FrameRectangleCertificate 8500 9000 (49/100) (981/2000) lowTIParameters60 where
  full := (22002247009/200000000000)
  energy := (173416455359/250000000000)
  cov := (147549461799/500000000000)
  schur := (1033239939751/1000000000000)
  cap := (970619563/1000000000000)
  W2 := (3482991757081/1000000000000)
  V := (291802407/1000000000000)
  mass := (5370593/125000000000)
  rootN := (127060513373/125000000000)
  rootB := (15577383951/500000000000)
  rootU := (154751458969/250000000000)
  rootV := (3416444977/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_60.scalar_checked
  centre := fun n hn => lowFull2_60 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy60 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_60.bound (by norm_num) hn lowTIParameters60_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_61 : FrameRectangleCertificate 8500 9000 (981/2000) (491/1000) lowTIParameters61 where
  full := (27524933019/250000000000)
  energy := (346712867201/500000000000)
  cov := (230780531/781250000)
  schur := (1033429144067/1000000000000)
  cap := (485733971/500000000000)
  W2 := (108751919031/31250000000)
  V := (29209921/100000000000)
  mass := (2682373/62500000000)
  rootN := (1016577170739/1000000000000)
  rootB := (6233676097/200000000000)
  rootU := (123798841471/200000000000)
  rootV := (8545455079/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_61.scalar_checked
  centre := fun n hn => lowFull2_61 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy61 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_61.bound (by norm_num) hn lowTIParameters61_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_62 : FrameRectangleCertificate 8500 9000 (491/1000) (983/2000) lowTIParameters62 where
  full := (22037687189/200000000000)
  energy := (693185759367/1000000000000)
  cov := (295699236001/1000000000000)
  schur := (1033618447133/1000000000000)
  cap := (30384897/31250000000)
  W2 := (1738568672287/500000000000)
  V := (146198007/500000000000)
  mass := (8574959/200000000000)
  rootN := (50833513727/50000000000)
  rootB := (15590996633/500000000000)
  rootU := (154745824977/250000000000)
  rootV := (2137448881/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_62.scalar_checked
  centre := fun n hn => lowFull2_62 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy62 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_62.bound (by norm_num) hn lowTIParameters62_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_63 : FrameRectangleCertificate 8500 9000 (983/2000) (123/250) lowTIParameters63 where
  full := (110277349301/1000000000000)
  energy := (346472948127/500000000000)
  cov := (147999696281/500000000000)
  schur := (103380784863/100000000000)
  cap := (973165849/1000000000000)
  W2 := (3474219543623/1000000000000)
  V := (292692817/1000000000000)
  mass := (42834937/1000000000000)
  rootN := (50838170911/50000000000)
  rootB := (15597803123/500000000000)
  rootU := (309486559547/500000000000)
  rootV := (3421653501/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_63.scalar_checked
  centre := fun n hn => lowFull2_63 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy63 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_63.bound (by norm_num) hn lowTIParameters63_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_64 : FrameRectangleCertificate 8500 9000 (123/250) (197/400) lowTIParameters64 where
  full := (55183237409/500000000000)
  energy := (346353072493/500000000000)
  cov := (296299549363/1000000000000)
  schur := (1033997348253/1000000000000)
  cap := (487007693/500000000000)
  W2 := (3471307986083/1000000000000)
  V := (292989621/1000000000000)
  mass := (42798129/1000000000000)
  rootN := (508428300809/500000000000)
  rootB := (1950576223/62500000000)
  rootU := (618963670527/1000000000000)
  rootV := (17116939593/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_64.scalar_checked
  centre := fun n hn => lowFull2_64 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy64 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_64.bound (by norm_num) hn lowTIParameters64_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_65 : FrameRectangleCertificate 8500 9000 (197/400) (493/1000) lowTIParameters65 where
  full := (110455815197/1000000000000)
  energy := (346233252743/500000000000)
  cov := (296599706403/1000000000000)
  schur := (1034186945693/1000000000000)
  cap := (24371633/25000000000)
  W2 := (1734201325971/500000000000)
  V := (11731457/40000000000)
  mass := (1336379/31250000000)
  rootN := (1016949824571/1000000000000)
  rootB := (975713541/31250000000)
  rootU := (309477479937/500000000000)
  rootV := (17125607289/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_65.scalar_checked
  centre := fun n hn => lowFull2_65 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy65 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_65.bound (by norm_num) hn lowTIParameters65_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_66 : FrameRectangleCertificate 8500 9000 (493/1000) (987/2000) lowTIParameters66 where
  full := (55272686581/500000000000)
  energy := (8652837221/12500000000)
  cov := (296899863681/1000000000000)
  schur := (129297080081/125000000000)
  cap := (487857829/500000000000)
  W2 := (3465503521333/1000000000000)
  V := (293583229/1000000000000)
  mass := (5341589/125000000000)
  rootN := (1017043086919/1000000000000)
  rootB := (3123644759/100000000000)
  rootU := (154736748213/250000000000)
  rootV := (17134270601/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_66.scalar_checked
  centre := fun n hn => lowFull2_66 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy66 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_66.bound (by norm_num) hn lowTIParameters66_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_67 : FrameRectangleCertificate 8500 9000 (987/2000) (247/500) lowTIParameters67 where
  full := (110635151469/1000000000000)
  energy := (691987561493/1000000000000)
  cov := (148600010597/500000000000)
  schur := (129320804101/125000000000)
  cap := (244141601/250000000000)
  W2 := (692522114887/200000000000)
  V := (146940017/500000000000)
  mass := (42703677/1000000000000)
  rootN := (1017136388499/1000000000000)
  rootB := (244141113/7812500000)
  rootU := (309469887623/500000000000)
  rootV := (17142929563/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_67.scalar_checked
  centre := fun n hn => lowFull2_67 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy67 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_67.bound (by norm_num) hn lowTIParameters67_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_68 : FrameRectangleCertificate 8500 9000 (247/500) (989/2000) lowTIParameters68 where
  full := (110725152897/1000000000000)
  energy := (691748256849/1000000000000)
  cov := (74375044737/250000000000)
  schur := (206951264381/200000000000)
  cap := (488708783/500000000000)
  W2 := (3459723791549/1000000000000)
  V := (294176839/1000000000000)
  mass := (21338417/500000000000)
  rootN := (1017229729169/1000000000000)
  rootB := (31263678063/1000000000000)
  rootU := (618933312887/1000000000000)
  rootV := (3430316831/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_68.scalar_checked
  centre := fun n hn => lowFull2_68 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy68 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_68.bound (by norm_num) hn lowTIParameters68_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_69 : FrameRectangleCertificate 8500 9000 (989/2000) (99/200) lowTIParameters69 where
  full := (22163076051/200000000000)
  energy := (691509063673/1000000000000)
  cov := (297800336939/1000000000000)
  schur := (1034946307613/1000000000000)
  cap := (244567287/250000000000)
  W2 := (1728421576499/500000000000)
  V := (294473643/1000000000000)
  mass := (10663003/250000000000)
  rootN := (508661554379/500000000000)
  rootB := (31277294449/1000000000000)
  rootU := (309463805833/500000000000)
  rootV := (1072514647/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_69.scalar_checked
  centre := fun n hn => lowFull2_69 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy69 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_69.bound (by norm_num) hn lowTIParameters69_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_70 : FrameRectangleCertificate 8500 9000 (99/200) (991/2000) lowTIParameters70 where
  full := (5545291819/50000000000)
  energy := (691269981889/1000000000000)
  cov := (298100495163/1000000000000)
  schur := (129392048703/125000000000)
  cap := (979121157/1000000000000)
  W2 := (3453968639213/1000000000000)
  V := (294770449/1000000000000)
  mass := (10657263/250000000000)
  rootN := (3974283309/3906250000)
  rootB := (7822727933/250000000000)
  rootU := (154730669383/250000000000)
  rootV := (17168880249/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_70.scalar_checked
  centre := fun n hn => lowFull2_70 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy70 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_70.bound (by norm_num) hn lowTIParameters70_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_71 : FrameRectangleCertificate 8500 9000 (991/2000) (62/125) lowTIParameters71 where
  full := (27749131033/250000000000)
  energy := (345515505711/500000000000)
  cov := (149200326813/500000000000)
  schur := (129415820959/125000000000)
  cap := (1224967/1250000000)
  W2 := (3451100230761/1000000000000)
  V := (147533627/500000000000)
  mass := (42607809/1000000000000)
  rootN := (508754992033/500000000000)
  rootB := (3913066253/125000000000)
  rootU := (154729629121/250000000000)
  rootV := (8588760883/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_71.scalar_checked
  centre := fun n hn => lowFull2_71 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy71 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_71.bound (by norm_num) hn lowTIParameters71_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_72 : FrameRectangleCertificate 8500 9000 (62/125) (993/2000) lowTIParameters72 where
  full := (27771861601/250000000000)
  energy := (345396076099/500000000000)
  cov := (74675203081/250000000000)
  schur := (1035516841437/1000000000000)
  cap := (980826483/1000000000000)
  W2 := (3448237908217/1000000000000)
  V := (14768203/50000000000)
  mass := (851763/20000000000)
  rootN := (508801739737/500000000000)
  rootB := (31318149419/1000000000000)
  rootU := (123783026917/200000000000)
  rootV := (8593079483/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_72.scalar_checked
  centre := fun n hn => lowFull2_72 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy72 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_72.bound (by norm_num) hn lowTIParameters72_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_73 : FrameRectangleCertificate 8500 9000 (993/2000) (497/1000) lowTIParameters73 where
  full := (3474331441/31250000000)
  energy := (690553404141/1000000000000)
  cov := (37375121407/125000000000)
  schur := (1035707210637/1000000000000)
  cap := (245419953/250000000000)
  W2 := (1722690826137/500000000000)
  V := (147830433/500000000000)
  mass := (42569951/1000000000000)
  rootN := (1017697013181/1000000000000)
  rootB := (31331770011/1000000000000)
  rootU := (77364067243/125000000000)
  rootV := (4298697957/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_73.scalar_checked
  centre := fun n hn => lowFull2_73 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy73 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_73.bound (by norm_num) hn lowTIParameters73_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_74 : FrameRectangleCertificate 8500 9000 (497/1000) (199/400) lowTIParameters74 where
  full := (27817501551/250000000000)
  energy := (690314767177/1000000000000)
  cov := (11972045217/40000000000)
  schur := (1035897674983/1000000000000)
  cap := (122816699/125000000000)
  W2 := (860632860927/250000000000)
  V := (36994709/125000000000)
  mass := (425531/10000000000)
  rootN := (508895292517/500000000000)
  rootB := (31345391879/1000000000000)
  rootU := (618910732739/1000000000000)
  rootV := (8601710179/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_74.scalar_checked
  centre := fun n hn => lowFull2_74 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy74 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_74.bound (by norm_num) hn lowTIParameters74_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_75 : FrameRectangleCertificate 8500 9000 (199/400) (249/500) lowTIParameters75 where
  full := (22272329931/200000000000)
  energy := (690076241231/1000000000000)
  cov := (11984051593/40000000000)
  schur := (129511029271/125000000000)
  cap := (98338783/100000000000)
  W2 := (27517498107/8000000000)
  V := (148127239/500000000000)
  mass := (42537493/1000000000000)
  rootN := (1017884194871/1000000000000)
  rootB := (7839753783/250000000000)
  rootU := (1547274313/2500000000)
  rootV := (8606022281/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_75.scalar_checked
  centre := fun n hn => lowFull2_75 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy75 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_75.bound (by norm_num) hn lowTIParameters75_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_76 : FrameRectangleCertificate 8500 9000 (249/500) (997/2000) lowTIParameters76 where
  full := (111453539467/1000000000000)
  energy := (172459456557/250000000000)
  cov := (299901449461/1000000000000)
  schur := (1036278887913/1000000000000)
  cap := (196848507/200000000000)
  W2 := (3436849092191/1000000000000)
  V := (59310257/200000000000)
  mass := (8504607/200000000000)
  rootN := (508988921273/500000000000)
  rootB := (3921579989/125000000000)
  rootU := (61890952161/100000000000)
  rootV := (17220664477/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_76.scalar_checked
  centre := fun n hn => lowFull2_76 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy76 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_76.bound (by norm_num) hn lowTIParameters76_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_77 : FrameRectangleCertificate 8500 9000 (997/2000) (499/1000) lowTIParameters77 where
  full := (111545678673/1000000000000)
  energy := (344799761047/500000000000)
  cov := (300201609329/1000000000000)
  schur := (1036469635929/1000000000000)
  cap := (61568607/62500000000)
  W2 := (1717008455597/500000000000)
  V := (74212023/250000000000)
  mass := (42509637/1000000000000)
  rootN := (203614305581/200000000000)
  rootB := (3923283287/125000000000)
  rootU := (309455064159/500000000000)
  rootV := (8614640039/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_77.scalar_checked
  centre := fun n hn => lowFull2_77 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy77 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_77.bound (by norm_num) hn lowTIParameters77_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_78 : FrameRectangleCertificate 8500 9000 (499/1000) (999/2000) lowTIParameters78 where
  full := (22327614067/200000000000)
  energy := (344680664379/500000000000)
  cov := (30050176943/100000000000)
  schur := (1036660477943/1000000000000)
  cap := (492976683/500000000000)
  W2 := (3431190701517/1000000000000)
  V := (297144899/1000000000000)
  mass := (42497219/1000000000000)
  rootN := (254541312701/250000000000)
  rootB := (31399894363/1000000000000)
  rootU := (309455775867/500000000000)
  rootV := (8618945687/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_78.scalar_checked
  centre := fun n hn => lowFull2_78 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy78 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_78.bound (by norm_num) hn lowTIParameters78_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_79 : FrameRectangleCertificate 8500 9000 (999/2000) (1/2) lowTIParameters79 where
  full := (111730717541/1000000000000)
  energy := (689123246139/1000000000000)
  cov := (75200482441/250000000000)
  schur := (259212853413/250000000000)
  cap := (30837797/31250000000)
  W2 := (1714185222129/500000000000)
  V := (148720853/500000000000)
  mass := (21242853/500000000000)
  rootN := (254564752771/250000000000)
  rootB := (15706762111/500000000000)
  rootU := (309456899153/500000000000)
  rootV := (1724649837/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_79.scalar_checked
  centre := fun n hn => lowFull2_79 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy79 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_79.bound (by norm_num) hn lowTIParameters79_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_80 : FrameRectangleCertificate 8500 9000 (1/2) (1001/2000) lowTIParameters80 where
  full := (111823623411/1000000000000)
  energy := (688885274171/1000000000000)
  cov := (149244841427/500000000000)
  schur := (1028052513001/1000000000000)
  cap := (98197141/100000000000)
  W2 := (856389030187/250000000000)
  V := (295155289/1000000000000)
  mass := (4247503/100000000000)
  rootN := (506964622287/500000000000)
  rootB := (31336423057/1000000000000)
  rootU := (154729218641/250000000000)
  rootV := (17180084081/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_80.scalar_checked
  centre := fun n hn => lowFull2_80 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy80 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_80.bound (by norm_num) hn lowTIParameters80_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_81 : FrameRectangleCertificate 8500 9000 (1001/2000) (501/1000) lowTIParameters81 where
  full := (22383358219/200000000000)
  energy := (68864741277/100000000000)
  cov := (298787232209/1000000000000)
  schur := (205648393849/200000000000)
  cap := (98282333/100000000000)
  W2 := (3422747712203/1000000000000)
  V := (147724757/500000000000)
  mass := (42465127/1000000000000)
  rootN := (253505666757/250000000000)
  rootB := (15675006619/500000000000)
  rootU := (618920787079/1000000000000)
  rootV := (3437728983/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_81.scalar_checked
  centre := fun n hn => lowFull2_81 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy81 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_81.bound (by norm_num) hn lowTIParameters81_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_82 : FrameRectangleCertificate 8500 9000 (501/1000) (1003/2000) lowTIParameters82 where
  full := (112010223767/1000000000000)
  energy := (688409661873/1000000000000)
  cov := (299084781793/1000000000000)
  schur := (25710787939/25000000000)
  cap := (196735151/200000000000)
  W2 := (3419945200207/1000000000000)
  V := (14787187/50000000000)
  mass := (21227969/500000000000)
  rootN := (101411612627/100000000000)
  rootB := (31363605581/1000000000000)
  rootU := (61892554249/100000000000)
  rootV := (17197201517/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_82.scalar_checked
  centre := fun n hn => lowFull2_82 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy82 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_82.bound (by norm_num) hn lowTIParameters82_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_83 : FrameRectangleCertificate 8500 9000 (1003/2000) (251/500) lowTIParameters83 where
  full := (700649529/6250000000)
  energy := (3440860107/5000000000)
  cov := (74845582901/250000000000)
  schur := (8228969261/8000000000)
  cap := (984528693/1000000000000)
  W2 := (3417148566111/1000000000000)
  V := (148018983/500000000000)
  mass := (10611853/250000000000)
  rootN := (253552405533/250000000000)
  rootB := (3137720021/100000000000)
  rootU := (123786229499/200000000000)
  rootV := (2150719233/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_83.scalar_checked
  centre := fun n hn => lowFull2_83 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy83 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_83.bound (by norm_num) hn lowTIParameters83_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_84 : FrameRectangleCertificate 8500 9000 (251/500) (201/400) lowTIParameters84 where
  full := (112197896949/1000000000000)
  energy := (687934491279/1000000000000)
  cov := (59935976329/200000000000)
  schur := (102881088919/100000000000)
  cap := (985382153/1000000000000)
  W2 := (1707178895779/500000000000)
  V := (9260381/31250000000)
  mass := (5304937/125000000000)
  rootN := (1014303154481/1000000000000)
  rootB := (31390797267/1000000000000)
  rootU := (618937608847/1000000000000)
  rootV := (17214301961/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_84.scalar_checked
  centre := fun n hn => lowFull2_84 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy84 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_84.bound (by norm_num) hn lowTIParameters84_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_85 : FrameRectangleCertificate 8500 9000 (201/400) (503/1000) lowTIParameters85 where
  full := (28073035991/250000000000)
  energy := (171924267859/250000000000)
  cov := (299977431913/1000000000000)
  schur := (1029000711977/1000000000000)
  cap := (986236139/1000000000000)
  W2 := (3411572858189/1000000000000)
  V := (148313209/500000000000)
  mass := (10608037/250000000000)
  rootN := (101439672317/100000000000)
  rootB := (31404396811/1000000000000)
  rootU := (618944933363/1000000000000)
  rootV := (2152855727/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_85.scalar_checked
  centre := fun n hn => lowFull2_85 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy85 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_85.bound (by norm_num) hn lowTIParameters85_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_86 : FrameRectangleCertificate 8500 9000 (503/1000) (1007/2000) lowTIParameters86 where
  full := (112386668981/1000000000000)
  energy := (3437298809/5000000000)
  cov := (300274982407/1000000000000)
  schur := (10291906257/10000000000)
  cap := (987090659/1000000000000)
  W2 := (3408793747719/1000000000000)
  V := (59384129/200000000000)
  mass := (42425323/1000000000000)
  rootN := (1014490328047/1000000000000)
  rootB := (15708999483/500000000000)
  rootU := (61895312791/100000000000)
  rootV := (2153923183/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_86.scalar_checked
  centre := fun n hn => lowFull2_86 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy86 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_86.bound (by norm_num) hn lowTIParameters86_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_87 : FrameRectangleCertificate 8500 9000 (1007/2000) (63/125) lowTIParameters87 where
  full := (28120368833/250000000000)
  energy := (137444512459/200000000000)
  cov := (37571566641/125000000000)
  schur := (1029380630101/1000000000000)
  cap := (987945721/1000000000000)
  W2 := (3406020441943/1000000000000)
  V := (37151859/125000000000)
  mass := (42418983/1000000000000)
  rootN := (40583358759/40000000000)
  rootB := (31431603857/1000000000000)
  rootU := (154740549857/250000000000)
  rootV := (8619960441/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_87.scalar_checked
  centre := fun n hn => lowFull2_87 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy87 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_87.bound (by norm_num) hn lowTIParameters87_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_88 : FrameRectangleCertificate 8500 9000 (63/125) (1009/2000) lowTIParameters88 where
  full := (14072070797/125000000000)
  energy := (686985472849/1000000000000)
  cov := (300870084077/1000000000000)
  schur := (10295707249/10000000000)
  cap := (988801331/1000000000000)
  W2 := (425406615341/125000000000)
  V := (297509099/1000000000000)
  mass := (10603273/250000000000)
  rootN := (1014677645807/1000000000000)
  rootB := (3930651447/125000000000)
  rootU := (618972154907/1000000000000)
  rootV := (4312113019/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_88.scalar_checked
  centre := fun n hn => lowFull2_88 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy88 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_88.bound (by norm_num) hn lowTIParameters88_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_89 : FrameRectangleCertificate 8500 9000 (1009/2000) (101/200) lowTIParameters89 where
  full := (56335972751/500000000000)
  energy := (686748493389/1000000000000)
  cov := (18822977203/62500000000)
  schur := (514880454913/500000000000)
  cap := (989657497/1000000000000)
  W2 := (136019646883/40000000000)
  V := (148901663/500000000000)
  mass := (21203809/500000000000)
  rootN := (1014771358399/1000000000000)
  rootB := (6291764449/200000000000)
  rootU := (618983001399/1000000000000)
  rootV := (4314244763/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_89.scalar_checked
  centre := fun n hn => lowFull2_89 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy89 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_89.bound (by norm_num) hn lowTIParameters89_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_90 : FrameRectangleCertificate 8500 9000 (101/200) (1011/2000) lowTIParameters90 where
  full := (56383808067/500000000000)
  energy := (343255811921/500000000000)
  cov := (301465186649/1000000000000)
  schur := (128743898079/125000000000)
  cap := (495257113/500000000000)
  W2 := (679547034393/200000000000)
  V := (149048777/500000000000)
  mass := (42402529/1000000000000)
  rootN := (1014865106619/1000000000000)
  rootB := (7868108993/250000000000)
  rootU := (309497373009/500000000000)
  rootV := (17265501847/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_90.scalar_checked
  centre := fun n hn => lowFull2_90 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy90 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_90.bound (by norm_num) hn lowTIParameters90_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_91 : FrameRectangleCertificate 8500 9000 (1011/2000) (253/500) lowTIParameters91 where
  full := (56431790863/500000000000)
  energy := (137254972827/200000000000)
  cov := (9430085571/31250000000)
  schur := (515070774507/500000000000)
  cap := (495685763/500000000000)
  W2 := (848746226127/250000000000)
  V := (298391781/1000000000000)
  mass := (42397797/1000000000000)
  rootN := (253739722577/250000000000)
  rootB := (31486052881/1000000000000)
  rootU := (619007395941/1000000000000)
  rootV := (17274020407/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_91.scalar_checked
  centre := fun n hn => lowFull2_91 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy91 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_91.bound (by norm_num) hn lowTIParameters91_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_92 : FrameRectangleCertificate 8500 9000 (253/500) (1013/2000) lowTIParameters92 where
  full := (56479922881/500000000000)
  energy := (343019107099/500000000000)
  cov := (151030145059/500000000000)
  schur := (1030332002741/1000000000000)
  cap := (198445881/200000000000)
  W2 := (3392240351947/1000000000000)
  V := (298686009/1000000000000)
  mass := (42393397/1000000000000)
  rootN := (507526354671/500000000000)
  rootB := (15749836547/500000000000)
  rootU := (123804191681/200000000000)
  rootV := (17282534797/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_92.scalar_checked
  centre := fun n hn => lowFull2_92 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy92 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_92.bound (by norm_num) hn lowTIParameters92_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_93 : FrameRectangleCertificate 8500 9000 (1013/2000) (507/1000) lowTIParameters93 where
  full := (113056411757/1000000000000)
  energy := (685801673953/1000000000000)
  cov := (18897365137/62500000000)
  schur := (1030522545527/1000000000000)
  cap := (99308787/100000000000)
  W2 := (1694750748213/500000000000)
  V := (298980237/1000000000000)
  mass := (5298663/125000000000)
  rootN := (101514656357/100000000000)
  rootB := (15756648359/500000000000)
  rootU := (619035440691/1000000000000)
  rootV := (3458208999/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_93.scalar_checked
  centre := fun n hn => lowFull2_93 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy93 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_93.bound (by norm_num) hn lowTIParameters93_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_94 : FrameRectangleCertificate 8500 9000 (507/1000) (203/400) lowTIParameters94 where
  full := (56576641631/500000000000)
  energy := (171391310833/250000000000)
  cov := (302655394487/1000000000000)
  schur := (1030713177121/1000000000000)
  cap := (993946927/1000000000000)
  W2 := (846692080093/250000000000)
  V := (149637233/500000000000)
  mass := (8477099/200000000000)
  rootN := (1015240452859/1000000000000)
  rootB := (31526923843/1000000000000)
  rootU := (154762712543/250000000000)
  rootV := (3459910207/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_94.scalar_checked
  centre := fun n hn => lowFull2_94 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy94 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_94.bound (by norm_num) hn lowTIParameters94_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_95 : FrameRectangleCertificate 8500 9000 (203/400) (127/250) lowTIParameters95 where
  full := (7078153991/62500000000)
  energy := (685328922263/1000000000000)
  cov := (151476473503/500000000000)
  schur := (1030903897261/1000000000000)
  cap := (994806587/1000000000000)
  W2 := (3384040806151/1000000000000)
  V := (149784347/500000000000)
  mass := (42381951/1000000000000)
  rootN := (1015334377071/1000000000000)
  rootB := (31540554641/1000000000000)
  rootU := (619067194257/1000000000000)
  rootV := (8654026433/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_95.scalar_checked
  centre := fun n hn => lowFull2_95 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy95 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_95.bound (by norm_num) hn lowTIParameters95_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_96 : FrameRectangleCertificate 8500 9000 (127/250) (1017/2000) lowTIParameters96 where
  full := (3542123661/31250000000)
  energy := (685092710671/1000000000000)
  cov := (151625249873/500000000000)
  schur := (41243788227/40000000000)
  cap := (199133371/200000000000)
  W2 := (3381318936221/1000000000000)
  V := (299862923/1000000000000)
  mass := (42378651/1000000000000)
  rootN := (1015428336061/1000000000000)
  rootB := (246517103/7812500000)
  rootU := (619084480423/1000000000000)
  rootV := (2164568819/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_96.scalar_checked
  centre := fun n hn => lowFull2_96 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy96 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_96.bound (by norm_num) hn lowTIParameters96_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_97 : FrameRectangleCertificate 8500 9000 (1017/2000) (509/1000) lowTIParameters97 where
  full := (113445766797/1000000000000)
  energy := (342428304243/500000000000)
  cov := (30354805271/100000000000)
  schur := (1031285602109/1000000000000)
  cap := (996527739/1000000000000)
  W2 := (337860269313/100000000000)
  V := (9379911/31250000000)
  mass := (2118779/50000000000)
  rootN := (203104465939/200000000000)
  rootB := (15783913797/500000000000)
  rootU := (123820543243/200000000000)
  rootV := (1732504407/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_97.scalar_checked
  centre := fun n hn => lowFull2_97 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy97 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_97.bound (by norm_num) hn lowTIParameters97_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_98 : FrameRectangleCertificate 8500 9000 (509/1000) (1019/2000) lowTIParameters98 where
  full := (28385974117/250000000000)
  energy := (171155153909/250000000000)
  cov := (151922802947/500000000000)
  schur := (128934573289/125000000000)
  cap := (15584207/15625000000)
  W2 := (210993253721/62500000000)
  V := (300451381/1000000000000)
  mass := (42372719/1000000000000)
  rootN := (12695204473/12500000000)
  rootB := (31581470011/1000000000000)
  rootU := (154780477309/250000000000)
  rootV := (8666766713/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_98.scalar_checked
  centre := fun n hn => lowFull2_98 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy98 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_98.bound (by norm_num) hn lowTIParameters98_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_99 : FrameRectangleCertificate 8500 9000 (1019/2000) (51/100) lowTIParameters99 where
  full := (28410587469/250000000000)
  energy := (42774045753/62500000000)
  cov := (304143159301/1000000000000)
  schur := (1031667658027/1000000000000)
  cap := (998251391/1000000000000)
  W2 := (26353023579/7812500000)
  V := (300745611/1000000000000)
  mass := (21185027/500000000000)
  rootN := (25392760509/25000000000)
  rootB := (31595116569/1000000000000)
  rootU := (309571033573/500000000000)
  rootV := (3468403731/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_99.scalar_checked
  centre := fun n hn => lowFull2_99 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy99 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_99.bound (by norm_num) hn lowTIParameters99_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_100 : FrameRectangleCertificate 8500 9000 (51/100) (1021/2000) lowTIParameters100 where
  full := (56870565383/500000000000)
  energy := (684148957649/1000000000000)
  cov := (301809124683/1000000000000)
  schur := (255736835901/250000000000)
  cap := (99338409/100000000000)
  W2 := (3370487551563/1000000000000)
  V := (5968753/20000000000)
  mass := (10591893/250000000000)
  rootN := (252852148449/250000000000)
  rootB := (123117173/3906250000)
  rootU := (619163197669/1000000000000)
  rootV := (17275348043/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_100.scalar_checked
  centre := fun n hn => lowFull2_100 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy100 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_100.bound (by norm_num) hn lowTIParameters100_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_101 : FrameRectangleCertificate 8500 9000 (1021/2000) (511/1000) lowTIParameters101 where
  full := (113840242913/1000000000000)
  energy := (683913292373/1000000000000)
  cov := (60420819887/200000000000)
  schur := (1023136928747/1000000000000)
  cap := (994242389/1000000000000)
  W2 := (673558728567/200000000000)
  V := (298729329/1000000000000)
  mass := (21182629/500000000000)
  rootN := (505751156387/500000000000)
  rootB := (31531609363/1000000000000)
  rootU := (619185308597/1000000000000)
  rootV := (432094701/25000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_101.scalar_checked
  centre := fun n hn => lowFull2_101 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy101 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_101.bound (by norm_num) hn lowTIParameters101_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_102 : FrameRectangleCertificate 8500 9000 (511/1000) (1023/2000) lowTIParameters102 where
  full := (113939690131/1000000000000)
  energy := (683677736143/1000000000000)
  cov := (37799884301/125000000000)
  schur := (127915824987/125000000000)
  cap := (199020269/200000000000)
  W2 := (3365105274773/1000000000000)
  V := (299021009/1000000000000)
  mass := (21181551/500000000000)
  rootN := (50579803279/50000000000)
  rootB := (31545226977/1000000000000)
  rootU := (619208407781/1000000000000)
  rootV := (17292223947/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_102.scalar_checked
  centre := fun n hn => lowFull2_102 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy102 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_102.bound (by norm_num) hn lowTIParameters102_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_103 : FrameRectangleCertificate 8500 9000 (1023/2000) (64/125) lowTIParameters103 where
  full := (57019738131/500000000000)
  energy := (683442288889/1000000000000)
  cov := (151347024799/500000000000)
  schur := (1023516356777/1000000000000)
  cap := (99596097/100000000000)
  W2 := (3362422430331/1000000000000)
  V := (299312689/1000000000000)
  mass := (10590273/250000000000)
  rootN := (252922463017/250000000000)
  rootB := (15779424657/500000000000)
  rootU := (309616251563/500000000000)
  rootV := (865032787/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_103.scalar_checked
  centre := fun n hn => lowFull2_103 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy103 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_103.bound (by norm_num) hn lowTIParameters103_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_104 : FrameRectangleCertificate 8500 9000 (64/125) (41/80) lowTIParameters104 where
  full := (114139605187/1000000000000)
  energy := (683206950541/1000000000000)
  cov := (302989025003/1000000000000)
  schur := (51185309957/50000000000)
  cap := (996821267/1000000000000)
  W2 := (839936273147/250000000000)
  V := (299604369/1000000000000)
  mass := (42359217/1000000000000)
  rootN := (505891836053/500000000000)
  rootB := (61664993/1953125000)
  rootU := (77407200327/125000000000)
  rootV := (692363337/40000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_104.scalar_checked
  centre := fun n hn => lowFull2_104 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy104 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_104.bound (by norm_num) hn lowTIParameters104_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_105 : FrameRectangleCertificate 8500 9000 (41/80) (513/1000) lowTIParameters105 where
  full := (114240080817/1000000000000)
  energy := (341485860513/500000000000)
  cov := (18955250039/62500000000)
  schur := (1023896126739/1000000000000)
  cap := (997682247/1000000000000)
  W2 := (3357073244637/1000000000000)
  V := (5997921/20000000000)
  mass := (42357469/1000000000000)
  rootN := (1011877525563/1000000000000)
  rootB := (631722169/20000000000)
  rootU := (619283714283/1000000000000)
  rootV := (8658753519/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_105.scalar_checked
  centre := fun n hn => lowFull2_105 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy105 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_105.bound (by norm_num) hn lowTIParameters105_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_106 : FrameRectangleCertificate 8500 9000 (513/1000) (1027/2000) lowTIParameters106 where
  full := (57170453549/500000000000)
  energy := (27309464011/40000000000)
  cov := (151789488231/500000000000)
  schur := (512043069677/500000000000)
  cap := (12481799/12500000000)
  W2 := (3354406869711/1000000000000)
  V := (30018773/100000000000)
  mass := (21177919/500000000000)
  rootN := (1011971412321/1000000000000)
  rootB := (31599745569/1000000000000)
  rootU := (619310846231/1000000000000)
  rootV := (17325926527/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_106.scalar_checked
  centre := fun n hn => lowFull2_106 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy106 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_106.bound (by norm_num) hn lowTIParameters106_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_107 : FrameRectangleCertificate 8500 9000 (1027/2000) (257/500) lowTIParameters107 where
  full := (114442088011/1000000000000)
  energy := (136500317643/200000000000)
  cov := (75968488129/250000000000)
  schur := (1024276236709/1000000000000)
  cap := (99940629/100000000000)
  W2 := (3351745951003/1000000000000)
  V := (300479411/1000000000000)
  mass := (10588579/250000000000)
  rootN := (506032666117/500000000000)
  rootB := (31613387829/1000000000000)
  rootU := (77417375827/125000000000)
  rootV := (3466868391/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_107.scalar_checked
  centre := fun n hn => lowFull2_107 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy107 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_107.bound (by norm_num) hn lowTIParameters107_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_108 : FrameRectangleCertificate 8500 9000 (257/500) (1029/2000) lowTIParameters108 where
  full := (114543627571/1000000000000)
  energy := (85283335597/125000000000)
  cov := (152084464393/500000000000)
  schur := (128058302323/125000000000)
  cap := (250067343/250000000000)
  W2 := (669818094377/200000000000)
  V := (300771093/1000000000000)
  mass := (8470579/200000000000)
  rootN := (15814988831/15625000000)
  rootB := (31627035461/1000000000000)
  rootU := (619368203667/1000000000000)
  rootV := (17342753329/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_108.scalar_checked
  centre := fun n hn => lowFull2_108 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy108 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_108.bound (by norm_num) hn lowTIParameters108_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_109 : FrameRectangleCertificate 8500 9000 (1029/2000) (103/200) lowTIParameters109 where
  full := (57322764917/500000000000)
  energy := (682031889889/1000000000000)
  cov := (304463905269/1000000000000)
  schur := (256164171179/250000000000)
  cap := (62570823/62500000000)
  W2 := (3346440415739/1000000000000)
  V := (150531387/500000000000)
  mass := (42351569/1000000000000)
  rootN := (1012253271033/1000000000000)
  rootB := (31640688489/1000000000000)
  rootU := (77424805711/125000000000)
  rootV := (4337790149/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_109.scalar_checked
  centre := fun n hn => lowFull2_109 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy109 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_109.bound (by norm_num) hn lowTIParameters109_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_110 : FrameRectangleCertificate 8500 9000 (103/200) (1031/2000) lowTIParameters110 where
  full := (114747798879/1000000000000)
  energy := (681797203479/1000000000000)
  cov := (304758881967/1000000000000)
  schur := (1024847034867/1000000000000)
  cap := (250499423/250000000000)
  W2 := (1671897882989/500000000000)
  V := (60270891/200000000000)
  mass := (10587583/250000000000)
  rootN := (1012347289653/1000000000000)
  rootB := (31654347127/1000000000000)
  rootU := (61942974101/100000000000)
  rootV := (17359563791/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_110.scalar_checked
  centre := fun n hn => lowFull2_110 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy110 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_110.bound (by norm_num) hn lowTIParameters110_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_111 : FrameRectangleCertificate 8500 9000 (1031/2000) (129/250) lowTIParameters111 where
  full := (114850438833/1000000000000)
  energy := (340781312741/500000000000)
  cov := (152526929439/500000000000)
  schur := (1025037468809/1000000000000)
  cap := (1002862949/1000000000000)
  W2 := (3341156506231/1000000000000)
  V := (301646137/1000000000000)
  mass := (5293647/125000000000)
  rootN := (1012441340923/1000000000000)
  rootB := (31668011447/1000000000000)
  rootU := (24778483923/40000000000)
  rootV := (347359259/20000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_111.scalar_checked
  centre := fun n hn => lowFull2_111 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy111 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_111.bound (by norm_num) hn lowTIParameters111_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_112 : FrameRectangleCertificate 8500 9000 (129/250) (1033/2000) lowTIParameters112 where
  full := (57476726923/500000000000)
  energy := (340664077911/500000000000)
  cov := (305348836003/1000000000000)
  schur := (1025227986287/1000000000000)
  cap := (1003728951/1000000000000)
  W2 := (834630654997/250000000000)
  V := (301937819/1000000000000)
  mass := (661689/15625000000)
  rootN := (253133856177/250000000000)
  rootB := (990052551/31250000000)
  rootU := (77436940667/125000000000)
  rootV := (543011189/31250000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_112.scalar_checked
  centre := fun n hn => lowFull2_112 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy112 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_112.bound (by norm_num) hn lowTIParameters112_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_113 : FrameRectangleCertificate 8500 9000 (1033/2000) (517/1000) lowTIParameters113 where
  full := (23011369623/200000000000)
  energy := (681093794431/1000000000000)
  cov := (15282190667/50000000000)
  schur := (256354646767/250000000000)
  cap := (1004595707/1000000000000)
  W2 := (1667947045487/500000000000)
  V := (302229501/1000000000000)
  mass := (42347087/1000000000000)
  rootN := (1012629540883/1000000000000)
  rootB := (6339071563/200000000000)
  rootU := (619530031357/1000000000000)
  rootV := (17384749093/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_113.scalar_checked
  centre := fun n hn => lowFull2_113 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy113 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_113.bound (by norm_num) hn lowTIParameters113_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_114 : FrameRectangleCertificate 8500 9000 (517/1000) (207/400) lowTIParameters114 where
  full := (23032125173/200000000000)
  energy := (340429770619/500000000000)
  cov := (305938790889/1000000000000)
  schur := (1025609270919/1000000000000)
  cap := (502731611/500000000000)
  W2 := (666654180581/200000000000)
  V := (9453787/31250000000)
  mass := (1323317/31250000000)
  rootN := (40508947573/40000000000)
  rootB := (7927260017/250000000000)
  rootU := (309782812369/500000000000)
  rootV := (8696568059/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_114.scalar_checked
  centre := fun n hn => lowFull2_114 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy114 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_114.bound (by norm_num) hn lowTIParameters114_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_115 : FrameRectangleCertificate 8500 9000 (207/400) (259/500) lowTIParameters115 where
  full := (115264791361/1000000000000)
  energy := (680625396173/1000000000000)
  cov := (306233768651/1000000000000)
  schur := (128225004699/125000000000)
  cap := (1006331509/1000000000000)
  W2 := (1665326519771/500000000000)
  V := (151406433/500000000000)
  mass := (42345263/1000000000000)
  rootN := (506408934951/500000000000)
  rootB := (31722728587/1000000000000)
  rootU := (619602314149/1000000000000)
  rootV := (543797471/31250000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_115.scalar_checked
  centre := fun n hn => lowFull2_115 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy115 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_115.bound (by norm_num) hn lowTIParameters115_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_116 : FrameRectangleCertificate 8500 9000 (259/500) (1037/2000) lowTIParameters116 where
  full := (115369348903/1000000000000)
  energy := (680391359169/1000000000000)
  cov := (153264373311/500000000000)
  schur := (512995443433/500000000000)
  cap := (1007200577/1000000000000)
  W2 := (1664020242413/500000000000)
  V := (303104549/1000000000000)
  mass := (1058611/25000000000)
  rootN := (15826751289/15625000000)
  rootB := (31736423507/1000000000000)
  rootU := (123928021667/200000000000)
  rootV := (17409898019/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_116.scalar_checked
  centre := fun n hn => lowFull2_116 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy116 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_116.bound (by norm_num) hn lowTIParameters116_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_117 : FrameRectangleCertificate 8500 9000 (1037/2000) (519/1000) lowTIParameters117 where
  full := (115474302827/1000000000000)
  energy := (13603148603/20000000000)
  cov := (153411862403/500000000000)
  schur := (1026181818493/1000000000000)
  cap := (504035217/500000000000)
  W2 := (133017328903/40000000000)
  V := (37924529/125000000000)
  mass := (4234367/100000000000)
  rootN := (15828223859/15625000000)
  rootB := (6350024989/200000000000)
  rootU := (154919754021/250000000000)
  rootV := (8709136467/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_117.scalar_checked
  centre := fun n hn => lowFull2_117 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy117 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_117.bound (by norm_num) hn lowTIParameters117_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_118 : FrameRectangleCertificate 8500 9000 (519/1000) (1039/2000) lowTIParameters118 where
  full := (28894914377/250000000000)
  energy := (169980902263/250000000000)
  cov := (307118703199/1000000000000)
  schur := (4105491329/4000000000)
  cap := (100894109/100000000000)
  W2 := (5316529979/1600000000)
  V := (60737583/200000000000)
  mass := (846859/20000000000)
  rootN := (1013100603223/1000000000000)
  rootB := (635276661/20000000000)
  rootU := (24788761851/40000000000)
  rootV := (697065753/40000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_118.scalar_checked
  centre := fun n hn => lowFull2_118 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy118 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_118.bound (by norm_num) hn lowTIParameters118_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_119 : FrameRectangleCertificate 8500 9000 (1039/2000) (13/25) lowTIParameters119 where
  full := (57842708677/500000000000)
  energy := (135937979161/200000000000)
  cov := (153706840901/500000000000)
  schur := (513281963953/500000000000)
  cap := (1009812553/1000000000000)
  W2 := (1660117255883/500000000000)
  V := (303979599/1000000000000)
  mass := (10585569/250000000000)
  rootN := (506597455557/500000000000)
  rootB := (31777547939/1000000000000)
  rootU := (154940051957/250000000000)
  rootV := (8717505363/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_119.scalar_checked
  centre := fun n hn => lowFull2_119 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy119 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_119.bound (by norm_num) hn lowTIParameters119_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_120 : FrameRectangleCertificate 8500 9000 (13/25) (1041/2000) lowTIParameters120 where
  full := (11579158681/100000000000)
  energy := (135891258067/200000000000)
  cov := (305058151249/1000000000000)
  schur := (254479792659/250000000000)
  cap := (1004920041/1000000000000)
  W2 := (663528606267/200000000000)
  V := (150825191/500000000000)
  mass := (21170823/500000000000)
  rootN := (252229950967/250000000000)
  rootB := (3170047383/100000000000)
  rootU := (61980250973/100000000000)
  rootV := (17368085157/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_120.scalar_checked
  centre := fun n hn => lowFull2_120 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy120 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_120.bound (by norm_num) hn lowTIParameters120_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_121 : FrameRectangleCertificate 8500 9000 (1041/2000) (521/1000) lowTIParameters121 where
  full := (115898170363/1000000000000)
  energy := (5306428067/7812500000)
  cov := (38168822817/125000000000)
  schur := (254527193597/250000000000)
  cap := (1005788093/1000000000000)
  W2 := (663011355957/200000000000)
  V := (150969773/500000000000)
  mass := (661579/15625000000)
  rootN := (1009013763231/1000000000000)
  rootB := (15857081171/500000000000)
  rootU := (77480745131/125000000000)
  rootV := (8688203871/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_121.scalar_checked
  centre := fun n hn => lowFull2_121 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy121 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_121.bound (by norm_num) hn lowTIParameters121_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_122 : FrameRectangleCertificate 8500 9000 (521/1000) (1043/2000) lowTIParameters122 where
  full := (58002586267/500000000000)
  energy := (339494701229/500000000000)
  cov := (305643014027/1000000000000)
  schur := (509149229319/500000000000)
  cap := (503328493/500000000000)
  W2 := (828118935341/250000000000)
  V := (302228711/1000000000000)
  mass := (8468101/200000000000)
  rootN := (100910775373/100000000000)
  rootB := (31727858201/1000000000000)
  rootU := (619890570901/1000000000000)
  rootV := (4346181593/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_122.scalar_checked
  centre := fun n hn => lowFull2_122 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy122 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_122.bound (by norm_num) hn lowTIParameters122_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_123 : FrameRectangleCertificate 8500 9000 (1043/2000) (261/500) lowTIParameters123 where
  full := (116112597881/1000000000000)
  energy := (84844514989/125000000000)
  cov := (9560482679/31250000000)
  schur := (50924411159/50000000000)
  cap := (251881681/250000000000)
  W2 := (3309899900387/1000000000000)
  V := (75629469/250000000000)
  mass := (10584997/250000000000)
  rootN := (1009201775257/1000000000000)
  rootB := (15870780731/500000000000)
  rootU := (24797453939/40000000000)
  rootV := (17393041023/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_123.scalar_checked
  centre := fun n hn => lowFull2_123 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy123 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_123.bound (by norm_num) hn lowTIParameters123_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_124 : FrameRectangleCertificate 8500 9000 (261/500) (209/400) lowTIParameters124 where
  full := (58110225501/500000000000)
  energy := (678522944871/1000000000000)
  cov := (306227877633/1000000000000)
  schur := (509339033889/500000000000)
  cap := (504198661/500000000000)
  W2 := (10335403879/3125000000)
  V := (302807041/1000000000000)
  mass := (2646219/62500000000)
  rootN := (1009295827683/1000000000000)
  rootB := (635105447/20000000000)
  rootU := (619983303029/1000000000000)
  rootV := (17401351701/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_124.scalar_checked
  centre := fun n hn => lowFull2_124 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy124 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_124.bound (by norm_num) hn lowTIParameters124_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_125 : FrameRectangleCertificate 8500 9000 (209/400) (523/1000) lowTIParameters125 where
  full := (116328736531/1000000000000)
  energy := (33914493863/50000000000)
  cov := (306520309741/1000000000000)
  schur := (1018867992183/1000000000000)
  cap := (201853757/200000000000)
  W2 := (330476374839/100000000000)
  V := (151548103/500000000000)
  mass := (10584763/250000000000)
  rootN := (1009389910879/1000000000000)
  rootB := (6353798187/200000000000)
  rootU := (620031443867/1000000000000)
  rootV := (4352414603/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_125.scalar_checked
  centre := fun n hn => lowFull2_125 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy125 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_125.bound (by norm_num) hn lowTIParameters125_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_126 : FrameRectangleCertificate 8500 9000 (523/1000) (1047/2000) lowTIParameters126 where
  full := (116437459143/1000000000000)
  energy := (84757114627/125000000000)
  cov := (306812742057/1000000000000)
  schur := (509528998107/500000000000)
  cap := (1010141127/1000000000000)
  W2 := (206387712893/62500000000)
  V := (75846343/250000000000)
  mass := (42338627/1000000000000)
  rootN := (201896804949/200000000000)
  rootB := (31782717427/1000000000000)
  rootU := (19377524387/31250000000)
  rootV := (1741796119/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_126.scalar_checked
  centre := fun n hn => lowFull2_126 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy126 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_126.bound (by norm_num) hn lowTIParameters126_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_127 : FrameRectangleCertificate 8500 9000 (1047/2000) (131/250) lowTIParameters127 where
  full := (116546623547/1000000000000)
  energy := (169456016017/250000000000)
  cov := (153552587287/500000000000)
  schur := (1019248079621/1000000000000)
  cap := (252753589/250000000000)
  W2 := (3299648199517/1000000000000)
  V := (151837269/500000000000)
  mass := (4233823/100000000000)
  rootN := (1009578169149/1000000000000)
  rootB := (31796451941/1000000000000)
  rootU := (310065661009/500000000000)
  rootV := (4356565003/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_127.scalar_checked
  centre := fun n hn => lowFull2_127 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy127 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_127.bound (by norm_num) hn lowTIParameters127_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_128 : FrameRectangleCertificate 8500 9000 (131/250) (1049/2000) lowTIParameters128 where
  full := (116656234491/1000000000000)
  energy := (338795659173/500000000000)
  cov := (307397607297/1000000000000)
  schur := (1019438242197/1000000000000)
  cap := (1011888483/1000000000000)
  W2 := (1648549056349/500000000000)
  V := (37995463/125000000000)
  mass := (21168929/500000000000)
  rootN := (50483617199/50000000000)
  rootB := (397627433/12500000000)
  rootU := (4845180299/7812500000)
  rootV := (4358638721/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_128.scalar_checked
  centre := fun n hn => lowFull2_128 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy128 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_128.bound (by norm_num) hn lowTIParameters128_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_129 : FrameRectangleCertificate 8500 9000 (1049/2000) (21/40) lowTIParameters129 where
  full := (11676629677/100000000000)
  energy := (338679339891/500000000000)
  cov := (9615313757/31250000000)
  schur := (1019628483713/1000000000000)
  cap := (506381759/500000000000)
  W2 := (1647276565257/500000000000)
  V := (30425287/100000000000)
  mass := (42337509/1000000000000)
  rootN := (252441637279/250000000000)
  rootB := (3182394567/100000000000)
  rootU := (620236058741/1000000000000)
  rootV := (4360711453/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_129.scalar_checked
  centre := fun n hn => lowFull2_129 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy129 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_129.bound (by norm_num) hn lowTIParameters129_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_130 : FrameRectangleCertificate 8500 9000 (21/40) (1051/2000) lowTIParameters130 where
  full := (58438407603/500000000000)
  energy := (677126148311/1000000000000)
  cov := (38497809169/125000000000)
  schur := (509909401983/500000000000)
  cap := (1013639471/1000000000000)
  W2 := (164600661889/50000000000)
  V := (76135509/250000000000)
  mass := (21168591/500000000000)
  rootN := (1009860784449/1000000000000)
  rootB := (15918852589/500000000000)
  rootU := (19384071033/31250000000)
  rootV := (5453479/312500000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_130.scalar_checked
  centre := fun n hn => lowFull2_130 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy130 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_130.bound (by norm_num) hn lowTIParameters130_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_131 : FrameRectangleCertificate 8500 9000 (1051/2000) (263/500) lowTIParameters131 where
  full := (116987794669/1000000000000)
  energy := (676893723859/1000000000000)
  cov := (308274906683/1000000000000)
  schur := (1020009202713/1000000000000)
  cap := (1014516353/1000000000000)
  W2 := (328947841921/100000000000)
  V := (304831203/1000000000000)
  mass := (67739/1600000000)
  rootN := (126244381231/125000000000)
  rootB := (15925736663/500000000000)
  rootU := (155086432731/250000000000)
  rootV := (4364853971/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_131.scalar_checked
  centre := fun n hn => lowFull2_131 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy131 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_131.bound (by norm_num) hn lowTIParameters131_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_132 : FrameRectangleCertificate 8500 9000 (263/500) (1053/2000) lowTIParameters132 where
  full := (58549620031/500000000000)
  energy := (676661406363/1000000000000)
  cov := (308567340217/1000000000000)
  schur := (255049919943/250000000000)
  cap := (40615767/40000000000)
  W2 := (51358572809/15625000000)
  V := (30512037/100000000000)
  mass := (10584147/250000000000)
  rootN := (1010049345217/1000000000000)
  rootB := (15932625137/500000000000)
  rootU := (155100610529/250000000000)
  rootV := (54586547/3125000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_132.scalar_checked
  centre := fun n hn => lowFull2_132 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy132 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_132.bound (by norm_num) hn lowTIParameters132_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_133 : FrameRectangleCertificate 8500 9000 (1053/2000) (527/1000) lowTIParameters133 where
  full := (23442231267/200000000000)
  energy := (84553649469/125000000000)
  cov := (6177195479/20000000000)
  schur := (1020390234889/1000000000000)
  cap := (508136473/500000000000)
  W2 := (410552993041/125000000000)
  V := (305409537/1000000000000)
  mass := (21168159/500000000000)
  rootN := (50507183521/50000000000)
  rootB := (31879036153/1000000000000)
  rootU := (620460416473/1000000000000)
  rootV := (8737985137/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_133.scalar_checked
  centre := fun n hn => lowFull2_133 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy133 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_133.bound (by norm_num) hn lowTIParameters133_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_134 : FrameRectangleCertificate 8500 9000 (527/1000) (211/400) lowTIParameters134 where
  full := (11732354847/100000000000)
  energy := (16904927299/25000000000)
  cov := (154576103943/500000000000)
  schur := (1020580867889/1000000000000)
  cap := (254288169/250000000000)
  W2 := (3281904257941/1000000000000)
  V := (19106169/62500000000)
  mass := (8467213/200000000000)
  rootN := (1010238025363/1000000000000)
  rootB := (31892831107/1000000000000)
  rootU := (77564957987/125000000000)
  rootV := (17484241591/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_134.scalar_checked
  centre := fun n hn => lowFull2_134 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy134 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_134.bound (by norm_num) hn lowTIParameters134_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_135 : FrameRectangleCertificate 8500 9000 (211/400) (66/125) lowTIParameters135 where
  full := (58718210747/500000000000)
  energy := (135193018983/200000000000)
  cov := (309444642023/1000000000000)
  schur := (1020771578529/1000000000000)
  cap := (1018033379/1000000000000)
  W2 := (1639694792793/500000000000)
  V := (305987871/1000000000000)
  mass := (10583957/250000000000)
  rootN := (505166204959/500000000000)
  rootB := (6381327069/200000000000)
  rootU := (155145048587/250000000000)
  rootV := (17492508997/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_135.scalar_checked
  centre := fun n hn => lowFull2_135 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy135 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_135.bound (by norm_num) hn lowTIParameters135_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_136 : FrameRectangleCertificate 8500 9000 (66/125) (1057/2000) lowTIParameters136 where
  full := (117549780473/1000000000000)
  energy := (84466650569/125000000000)
  cov := (309737076359/1000000000000)
  schur := (1020962366607/1000000000000)
  cap := (509457531/500000000000)
  W2 := (655375982483/200000000000)
  V := (306277039/1000000000000)
  mass := (8467121/200000000000)
  rootN := (40417072959/40000000000)
  rootB := (7980112241/250000000000)
  rootU := (310321008933/500000000000)
  rootV := (8750386263/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_136.scalar_checked
  centre := fun n hn => lowFull2_136 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy136 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_136.bound (by norm_num) hn lowTIParameters136_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_137 : FrameRectangleCertificate 8500 9000 (1057/2000) (529/1000) lowTIParameters137 where
  full := (117663630513/1000000000000)
  energy := (675501420803/1000000000000)
  cov := (19376844431/62500000000)
  schur := (510576615953/500000000000)
  cap := (50989887/50000000000)
  W2 := (3274375223591/1000000000000)
  V := (306566207/1000000000000)
  mass := (10583849/250000000000)
  rootN := (1010521267419/1000000000000)
  rootB := (15967136093/500000000000)
  rootU := (620705144549/1000000000000)
  rootV := (3501806431/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_137.scalar_checked
  centre := fun n hn => lowFull2_137 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy137 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_137.bound (by norm_num) hn lowTIParameters137_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_138 : FrameRectangleCertificate 8500 9000 (529/1000) (1059/2000) lowTIParameters138 where
  full := (29444494189/250000000000)
  energy := (675269743601/1000000000000)
  cov := (310321945629/1000000000000)
  schur := (510672087109/500000000000)
  cap := (1020681421/1000000000000)
  W2 := (3271875504383/1000000000000)
  V := (2454843/8000000000)
  mass := (52919/1250000000)
  rootN := (50530787007/50000000000)
  rootB := (7987026281/250000000000)
  rootU := (77596198069/125000000000)
  rootV := (1751728789/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_138.scalar_checked
  centre := fun n hn => lowFull2_138 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy138 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_138.bound (by norm_num) hn lowTIParameters138_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_139 : FrameRectangleCertificate 8500 9000 (1059/2000) (53/100) lowTIParameters139 where
  full := (23578564879/200000000000)
  energy := (168759543219/250000000000)
  cov := (310614380561/1000000000000)
  schur := (1021535193329/1000000000000)
  cap := (204313223/200000000000)
  W2 := (653876148003/200000000000)
  V := (307144543/1000000000000)
  mass := (5291877/125000000000)
  rootN := (1010710242023/1000000000000)
  rootB := (31961947923/1000000000000)
  rootU := (620835348111/1000000000000)
  rootV := (3505107947/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_139.scalar_checked
  centre := fun n hn => lowFull2_139 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy139 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_139.bound (by norm_num) hn lowTIParameters139_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_140 : FrameRectangleCertificate 8500 9000 (53/100) (1061/2000) lowTIParameters140 where
  full := (59004089329/500000000000)
  energy := (134961341713/200000000000)
  cov := (77059409789/250000000000)
  schur := (1012963141557/1000000000000)
  cap := (254163251/250000000000)
  W2 := (326689091591/100000000000)
  V := (19049647/62500000000)
  mass := (42334843/1000000000000)
  rootN := (503230350227/500000000000)
  rootB := (6376999307/200000000000)
  rootU := (620902445527/1000000000000)
  rootV := (17458360519/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_140.scalar_checked
  centre := fun n hn => lowFull2_140 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy140 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_140.bound (by norm_num) hn lowTIParameters140_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_141 : FrameRectangleCertificate 8500 9000 (1061/2000) (531/1000) lowTIParameters141 where
  full := (11812404481/100000000000)
  energy := (168643837649/250000000000)
  cov := (154263778583/500000000000)
  schur := (253288166247/250000000000)
  cap := (15898981/15625000000)
  W2 := (204025376089/62500000000)
  V := (305081031/1000000000000)
  mass := (42334681/1000000000000)
  rootN := (1006554849469/1000000000000)
  rootB := (6379764209/200000000000)
  rootU := (77621360893/125000000000)
  rootV := (8733284477/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_141.scalar_checked
  centre := fun n hn => lowFull2_141 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy141 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_141.bound (by norm_num) hn lowTIParameters141_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_142 : FrameRectangleCertificate 8500 9000 (531/1000) (1063/2000) lowTIParameters142 where
  full := (59120214081/500000000000)
  energy := (134868819781/200000000000)
  cov := (308817475369/1000000000000)
  schur := (1013342263941/1000000000000)
  cap := (63651101/62500000000)
  W2 := (3261926030057/1000000000000)
  V := (305367711/1000000000000)
  mass := (661477/15625000000)
  rootN := (100664902719/100000000000)
  rootB := (1994541003/62500000000)
  rootU := (621040683391/1000000000000)
  rootV := (17474773561/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_142.scalar_checked
  centre := fun n hn => lowFull2_142 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy142 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_142.bound (by norm_num) hn lowTIParameters142_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_143 : FrameRectangleCertificate 8500 9000 (1063/2000) (133/250) lowTIParameters143 where
  full := (118357334069/1000000000000)
  energy := (674112953423/1000000000000)
  cov := (38638424221/125000000000)
  schur := (506765969107/500000000000)
  cap := (1019301507/1000000000000)
  W2 := (3259450939299/1000000000000)
  V := (30565439/100000000000)
  mass := (8466877/200000000000)
  rootN := (251685808377/250000000000)
  rootB := (31926501641/1000000000000)
  rootU := (621111844763/1000000000000)
  rootV := (1748297429/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_143.scalar_checked
  centre := fun n hn => lowFull2_143 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy143 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_143.bound (by norm_num) hn lowTIParameters143_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_144 : FrameRectangleCertificate 8500 9000 (133/250) (213/400) lowTIParameters144 where
  full := (118474767923/1000000000000)
  energy := (336940957041/500000000000)
  cov := (309397312361/1000000000000)
  schur := (2534304219/2500000000)
  cap := (1020186471/1000000000000)
  W2 := (407122591341/125000000000)
  V := (30594107/100000000000)
  mass := (169337/4000000000)
  rootN := (503418734157/500000000000)
  rootB := (31940358029/1000000000000)
  rootU := (621184381809/1000000000000)
  rootV := (8745585601/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_144.scalar_checked
  centre := fun n hn => lowFull2_144 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy144 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_144.bound (by norm_num) hn lowTIParameters144_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_145 : FrameRectangleCertificate 8500 9000 (213/400) (533/1000) lowTIParameters145 where
  full := (59296367581/500000000000)
  energy := (673650980819/1000000000000)
  cov := (77421807787/250000000000)
  schur := (506955755953/500000000000)
  cap := (25526813/25000000000)
  W2 := (650903078003/200000000000)
  V := (306227751/1000000000000)
  mass := (42334123/1000000000000)
  rootN := (1006931731503/1000000000000)
  rootB := (15977112693/500000000000)
  rootU := (621258305159/1000000000000)
  rootV := (17499364303/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_145.scalar_checked
  centre := fun n hn => lowFull2_145 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy145 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_145.bound (by norm_num) hn lowTIParameters145_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_146 : FrameRectangleCertificate 8500 9000 (533/1000) (1067/2000) lowTIParameters146 where
  full := (59355620629/500000000000)
  energy := (336710076781/500000000000)
  cov := (309977150129/1000000000000)
  schur := (253525352731/250000000000)
  cap := (63872479/62500000000)
  W2 := (8130137257/2500000000)
  V := (306514431/1000000000000)
  mass := (10583501/250000000000)
  rootN := (1007026022963/1000000000000)
  rootB := (15984051927/500000000000)
  rootU := (621333625479/1000000000000)
  rootV := (8753776771/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_146.scalar_checked
  centre := fun n hn => lowFull2_146 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy146 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_146.bound (by norm_num) hn lowTIParameters146_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_147 : FrameRectangleCertificate 8500 9000 (1067/2000) (267/500) lowTIParameters147 where
  full := (23766058347/200000000000)
  energy := (2692757729/4000000000)
  cov := (310267069303/1000000000000)
  schur := (1014291384467/1000000000000)
  cap := (255711979/250000000000)
  W2 := (3249599254919/1000000000000)
  V := (306801111/1000000000000)
  mass := (42333893/1000000000000)
  rootN := (201424068519/200000000000)
  rootB := (15990996811/500000000000)
  rootU := (310705176769/500000000000)
  rootV := (2189467369/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_147.scalar_checked
  centre := fun n hn => lowFull2_147 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy147 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_147.bound (by norm_num) hn lowTIParameters147_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_148 : FrameRectangleCertificate 8500 9000 (267/500) (1069/2000) lowTIParameters148 where
  full := (118949892153/1000000000000)
  energy := (168239704203/250000000000)
  cov := (310556988669/1000000000000)
  schur := (253620358079/250000000000)
  cap := (204747457/200000000000)
  W2 := (3247148432103/1000000000000)
  V := (19192987/62500000000)
  mass := (42333787/1000000000000)
  rootN := (1007214690281/1000000000000)
  rootB := (6399178963/200000000000)
  rootU := (310744250069/500000000000)
  rootV := (8761960283/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_148.scalar_checked
  centre := fun n hn => lowFull2_148 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy148 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_148.bound (by norm_num) hn lowTIParameters148_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_149 : FrameRectangleCertificate 8500 9000 (1069/2000) (107/200) lowTIParameters149 where
  full := (2976751203/25000000000)
  energy := (336364153591/500000000000)
  cov := (155423454113/500000000000)
  schur := (1014671554273/1000000000000)
  cap := (1024627789/1000000000000)
  W2 := (3244702420231/1000000000000)
  V := (307374473/1000000000000)
  mass := (42333689/1000000000000)
  rootN := (201461813183/200000000000)
  rootB := (32009807701/1000000000000)
  rootU := (621568076169/1000000000000)
  rootV := (17532098363/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_149.scalar_checked
  centre := fun n hn => lowFull2_149 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy149 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_149.bound (by norm_num) hn lowTIParameters149_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_150 : FrameRectangleCertificate 8500 9000 (107/200) (1071/2000) lowTIParameters150 where
  full := (59595382641/500000000000)
  energy := (10507779739/15625000000)
  cov := (155568413989/500000000000)
  schur := (1014861750167/1000000000000)
  cap := (205103887/200000000000)
  W2 := (3242261205231/1000000000000)
  V := (153830577/500000000000)
  mass := (10583399/250000000000)
  rootN := (251850867351/250000000000)
  rootB := (8005933093/250000000000)
  rootU := (621649092573/1000000000000)
  rootV := (17540272347/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_150.scalar_checked
  centre := fun n hn => lowFull2_150 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy150 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_150.bound (by norm_num) hn lowTIParameters150_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_151 : FrameRectangleCertificate 8500 9000 (1071/2000) (67/125) lowTIParameters151 where
  full := (119312049329/1000000000000)
  energy := (134453521017/200000000000)
  cov := (311426747917/1000000000000)
  schur := (101505201977/100000000000)
  cap := (1026412237/1000000000000)
  W2 := (3239824773089/1000000000000)
  V := (61589567/200000000000)
  mass := (10583377/250000000000)
  rootN := (1007497900629/1000000000000)
  rootB := (4004708629/125000000000)
  rootU := (310865780179/500000000000)
  rootV := (4387110631/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_151.scalar_checked
  centre := fun n hn => lowFull2_151 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy151 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_151.bound (by norm_num) hn lowTIParameters151_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_152 : FrameRectangleCertificate 8500 9000 (67/125) (1073/2000) lowTIParameters152 where
  full := (59716952999/500000000000)
  energy := (336018706243/500000000000)
  cov := (19482291753/62500000000)
  schur := (507621181453/500000000000)
  cap := (513653103/500000000000)
  W2 := (809348277457/250000000000)
  V := (308234517/1000000000000)
  mass := (21166713/500000000000)
  rootN := (251898089873/250000000000)
  rootB := (16025808919/500000000000)
  rootU := (621815490607/1000000000000)
  rootV := (17556608927/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_152.scalar_checked
  centre := fun n hn => lowFull2_152 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy152 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_152.bound (by norm_num) hn lowTIParameters152_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_153 : FrameRectangleCertificate 8500 9000 (1073/2000) (537/1000) lowTIParameters153 where
  full := (23911268213/200000000000)
  energy := (167951831357/250000000000)
  cov := (312006588369/1000000000000)
  schur := (1015432779361/1000000000000)
  cap := (205640271/200000000000)
  W2 := (3234966201489/1000000000000)
  V := (154260599/500000000000)
  mass := (10583337/250000000000)
  rootN := (1007686845881/1000000000000)
  rootB := (1282623159/40000000000)
  rootU := (155475223613/250000000000)
  rootV := (3512954301/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_153.scalar_checked
  centre := fun n hn => lowFull2_153 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy153 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_153.bound (by norm_num) hn lowTIParameters153_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_154 : FrameRectangleCertificate 8500 9000 (537/1000) (43/80) lowTIParameters154 where
  full := (119679360347/1000000000000)
  energy := (13431546877/20000000000)
  cov := (3903706361/12500000000)
  schur := (507811634483/500000000000)
  cap := (1029097697/1000000000000)
  W2 := (3232544034271/1000000000000)
  V := (7720197/25000000000)
  mass := (1693331/40000000000)
  rootN := (125972669963/125000000000)
  rootB := (32079552631/1000000000000)
  rootU := (155496945773/250000000000)
  rootV := (219661629/12500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_154.scalar_checked
  centre := fun n hn => lowFull2_154 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy154 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_154.bound (by norm_num) hn lowTIParameters154_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_155 : FrameRectangleCertificate 8500 9000 (43/80) (269/500) lowTIParameters155 where
  full := (119802969713/1000000000000)
  energy := (671347467681/1000000000000)
  cov := (15629321479/50000000000)
  schur := (1015813831501/1000000000000)
  cap := (257498811/250000000000)
  W2 := (807531648577/250000000000)
  V := (154547281/500000000000)
  mass := (42333207/1000000000000)
  rootN := (251968975211/250000000000)
  rootB := (1002923093/31250000000)
  rootU := (311038083901/500000000000)
  rootV := (4395271337/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_155.scalar_checked
  centre := fun n hn => lowFull2_155 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy155 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_155.bound (by norm_num) hn lowTIParameters155_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_156 : FrameRectangleCertificate 8500 9000 (269/500) (1077/2000) lowTIParameters156 where
  full := (59963587537/500000000000)
  energy := (33555884843/50000000000)
  cov := (31287635047/100000000000)
  schur := (1016004466801/1000000000000)
  cap := (1030894009/1000000000000)
  W2 := (3227713867887/1000000000000)
  V := (61876249/200000000000)
  mass := (21166571/500000000000)
  rootN := (1007970469211/1000000000000)
  rootB := (8026884549/250000000000)
  rootU := (311083029963/500000000000)
  rootV := (1099327289/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_156.scalar_checked
  centre := fun n hn => lowFull2_156 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy156 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_156.bound (by norm_num) hn lowTIParameters156_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_157 : FrameRectangleCertificate 8500 9000 (1077/2000) (539/1000) lowTIParameters157 where
  full := (120051982381/1000000000000)
  energy := (670888031319/1000000000000)
  cov := (313166271547/1000000000000)
  schur := (1016195174659/1000000000000)
  cap := (1031794003/1000000000000)
  W2 := (806326460329/250000000000)
  V := (309667927/1000000000000)
  mass := (42333081/1000000000000)
  rootN := (126008133087/125000000000)
  rootB := (16060775223/500000000000)
  rootU := (77782183857/125000000000)
  rootV := (549918253/31250000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_157.scalar_checked
  centre := fun n hn => lowFull2_157 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy157 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_157.bound (by norm_num) hn lowTIParameters157_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_158 : FrameRectangleCertificate 8500 9000 (539/1000) (1079/2000) lowTIParameters158 where
  full := (30044349407/250000000000)
  energy := (670658470991/1000000000000)
  cov := (31345619281/100000000000)
  schur := (508192977439/500000000000)
  cap := (25817381/25000000000)
  W2 := (402862812613/125000000000)
  V := (30995461/100000000000)
  mass := (1322907/31250000000)
  rootN := (126019960899/125000000000)
  rootB := (1285423037/40000000000)
  rootU := (622350412041/1000000000000)
  rootV := (8802763913/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_158.scalar_checked
  centre := fun n hn => lowFull2_158 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy158 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_158.bound (by norm_num) hn lowTIParameters158_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle2_159 : FrameRectangleCertificate 8500 9000 (1079/2000) (27/50) lowTIParameters159 where
  full := (6015171343/50000000000)
  energy := (670429015813/1000000000000)
  cov := (156873057131/500000000000)
  schur := (1016576807277/1000000000000)
  cap := (1033597733/1000000000000)
  W2 := (3220503833081/1000000000000)
  V := (77560323/250000000000)
  mass := (4233297/100000000000)
  rootN := (1008254336603/1000000000000)
  rootB := (32149614819/1000000000000)
  rootU := (31122244751/50000000000)
  rootV := (8806833881/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness2_159.scalar_checked
  centre := fun n hn => lowFull2_159 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy159 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness2_159.bound (by norm_num) hn lowTIParameters159_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangles2 (j : Fin 160) :
    FrameRectangleCertificate 8500 9000 (frameNoiseLower j) (frameNoiseUpper j) (lowTIParameters j) := by
  match j with
  | ⟨0,_⟩ => convert lowRectangle2_0 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨1,_⟩ => convert lowRectangle2_1 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨2,_⟩ => convert lowRectangle2_2 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨3,_⟩ => convert lowRectangle2_3 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨4,_⟩ => convert lowRectangle2_4 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨5,_⟩ => convert lowRectangle2_5 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨6,_⟩ => convert lowRectangle2_6 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨7,_⟩ => convert lowRectangle2_7 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨8,_⟩ => convert lowRectangle2_8 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨9,_⟩ => convert lowRectangle2_9 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨10,_⟩ => convert lowRectangle2_10 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨11,_⟩ => convert lowRectangle2_11 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨12,_⟩ => convert lowRectangle2_12 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨13,_⟩ => convert lowRectangle2_13 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨14,_⟩ => convert lowRectangle2_14 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨15,_⟩ => convert lowRectangle2_15 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨16,_⟩ => convert lowRectangle2_16 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨17,_⟩ => convert lowRectangle2_17 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨18,_⟩ => convert lowRectangle2_18 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨19,_⟩ => convert lowRectangle2_19 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨20,_⟩ => convert lowRectangle2_20 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨21,_⟩ => convert lowRectangle2_21 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨22,_⟩ => convert lowRectangle2_22 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨23,_⟩ => convert lowRectangle2_23 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨24,_⟩ => convert lowRectangle2_24 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨25,_⟩ => convert lowRectangle2_25 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨26,_⟩ => convert lowRectangle2_26 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨27,_⟩ => convert lowRectangle2_27 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨28,_⟩ => convert lowRectangle2_28 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨29,_⟩ => convert lowRectangle2_29 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨30,_⟩ => convert lowRectangle2_30 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨31,_⟩ => convert lowRectangle2_31 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨32,_⟩ => convert lowRectangle2_32 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨33,_⟩ => convert lowRectangle2_33 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨34,_⟩ => convert lowRectangle2_34 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨35,_⟩ => convert lowRectangle2_35 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨36,_⟩ => convert lowRectangle2_36 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨37,_⟩ => convert lowRectangle2_37 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨38,_⟩ => convert lowRectangle2_38 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨39,_⟩ => convert lowRectangle2_39 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨40,_⟩ => convert lowRectangle2_40 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨41,_⟩ => convert lowRectangle2_41 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨42,_⟩ => convert lowRectangle2_42 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨43,_⟩ => convert lowRectangle2_43 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨44,_⟩ => convert lowRectangle2_44 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨45,_⟩ => convert lowRectangle2_45 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨46,_⟩ => convert lowRectangle2_46 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨47,_⟩ => convert lowRectangle2_47 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨48,_⟩ => convert lowRectangle2_48 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨49,_⟩ => convert lowRectangle2_49 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨50,_⟩ => convert lowRectangle2_50 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨51,_⟩ => convert lowRectangle2_51 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨52,_⟩ => convert lowRectangle2_52 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨53,_⟩ => convert lowRectangle2_53 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨54,_⟩ => convert lowRectangle2_54 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨55,_⟩ => convert lowRectangle2_55 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨56,_⟩ => convert lowRectangle2_56 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨57,_⟩ => convert lowRectangle2_57 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨58,_⟩ => convert lowRectangle2_58 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨59,_⟩ => convert lowRectangle2_59 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨60,_⟩ => convert lowRectangle2_60 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨61,_⟩ => convert lowRectangle2_61 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨62,_⟩ => convert lowRectangle2_62 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨63,_⟩ => convert lowRectangle2_63 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨64,_⟩ => convert lowRectangle2_64 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨65,_⟩ => convert lowRectangle2_65 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨66,_⟩ => convert lowRectangle2_66 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨67,_⟩ => convert lowRectangle2_67 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨68,_⟩ => convert lowRectangle2_68 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨69,_⟩ => convert lowRectangle2_69 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨70,_⟩ => convert lowRectangle2_70 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨71,_⟩ => convert lowRectangle2_71 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨72,_⟩ => convert lowRectangle2_72 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨73,_⟩ => convert lowRectangle2_73 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨74,_⟩ => convert lowRectangle2_74 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨75,_⟩ => convert lowRectangle2_75 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨76,_⟩ => convert lowRectangle2_76 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨77,_⟩ => convert lowRectangle2_77 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨78,_⟩ => convert lowRectangle2_78 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨79,_⟩ => convert lowRectangle2_79 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨80,_⟩ => convert lowRectangle2_80 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨81,_⟩ => convert lowRectangle2_81 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨82,_⟩ => convert lowRectangle2_82 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨83,_⟩ => convert lowRectangle2_83 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨84,_⟩ => convert lowRectangle2_84 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨85,_⟩ => convert lowRectangle2_85 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨86,_⟩ => convert lowRectangle2_86 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨87,_⟩ => convert lowRectangle2_87 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨88,_⟩ => convert lowRectangle2_88 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨89,_⟩ => convert lowRectangle2_89 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨90,_⟩ => convert lowRectangle2_90 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨91,_⟩ => convert lowRectangle2_91 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨92,_⟩ => convert lowRectangle2_92 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨93,_⟩ => convert lowRectangle2_93 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨94,_⟩ => convert lowRectangle2_94 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨95,_⟩ => convert lowRectangle2_95 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨96,_⟩ => convert lowRectangle2_96 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨97,_⟩ => convert lowRectangle2_97 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨98,_⟩ => convert lowRectangle2_98 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨99,_⟩ => convert lowRectangle2_99 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨100,_⟩ => convert lowRectangle2_100 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨101,_⟩ => convert lowRectangle2_101 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨102,_⟩ => convert lowRectangle2_102 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨103,_⟩ => convert lowRectangle2_103 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨104,_⟩ => convert lowRectangle2_104 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨105,_⟩ => convert lowRectangle2_105 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨106,_⟩ => convert lowRectangle2_106 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨107,_⟩ => convert lowRectangle2_107 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨108,_⟩ => convert lowRectangle2_108 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨109,_⟩ => convert lowRectangle2_109 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨110,_⟩ => convert lowRectangle2_110 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨111,_⟩ => convert lowRectangle2_111 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨112,_⟩ => convert lowRectangle2_112 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨113,_⟩ => convert lowRectangle2_113 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨114,_⟩ => convert lowRectangle2_114 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨115,_⟩ => convert lowRectangle2_115 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨116,_⟩ => convert lowRectangle2_116 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨117,_⟩ => convert lowRectangle2_117 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨118,_⟩ => convert lowRectangle2_118 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨119,_⟩ => convert lowRectangle2_119 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨120,_⟩ => convert lowRectangle2_120 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨121,_⟩ => convert lowRectangle2_121 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨122,_⟩ => convert lowRectangle2_122 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨123,_⟩ => convert lowRectangle2_123 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨124,_⟩ => convert lowRectangle2_124 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨125,_⟩ => convert lowRectangle2_125 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨126,_⟩ => convert lowRectangle2_126 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨127,_⟩ => convert lowRectangle2_127 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨128,_⟩ => convert lowRectangle2_128 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨129,_⟩ => convert lowRectangle2_129 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨130,_⟩ => convert lowRectangle2_130 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨131,_⟩ => convert lowRectangle2_131 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨132,_⟩ => convert lowRectangle2_132 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨133,_⟩ => convert lowRectangle2_133 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨134,_⟩ => convert lowRectangle2_134 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨135,_⟩ => convert lowRectangle2_135 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨136,_⟩ => convert lowRectangle2_136 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨137,_⟩ => convert lowRectangle2_137 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨138,_⟩ => convert lowRectangle2_138 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨139,_⟩ => convert lowRectangle2_139 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨140,_⟩ => convert lowRectangle2_140 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨141,_⟩ => convert lowRectangle2_141 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨142,_⟩ => convert lowRectangle2_142 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨143,_⟩ => convert lowRectangle2_143 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨144,_⟩ => convert lowRectangle2_144 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨145,_⟩ => convert lowRectangle2_145 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨146,_⟩ => convert lowRectangle2_146 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨147,_⟩ => convert lowRectangle2_147 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨148,_⟩ => convert lowRectangle2_148 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨149,_⟩ => convert lowRectangle2_149 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨150,_⟩ => convert lowRectangle2_150 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨151,_⟩ => convert lowRectangle2_151 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨152,_⟩ => convert lowRectangle2_152 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨153,_⟩ => convert lowRectangle2_153 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨154,_⟩ => convert lowRectangle2_154 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨155,_⟩ => convert lowRectangle2_155 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨156,_⟩ => convert lowRectangle2_156 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨157,_⟩ => convert lowRectangle2_157 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨158,_⟩ => convert lowRectangle2_158 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨159,_⟩ => convert lowRectangle2_159 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨j+160,h⟩ => exact False.elim (by omega)
end BstLean.BlueprintLow
