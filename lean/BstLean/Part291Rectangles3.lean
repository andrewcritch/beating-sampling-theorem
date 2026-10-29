import BstLean.Part291Rectangle
import BstLean.Part291Certificates3
import BstLean.Part291LocalEnergyBatch0
import BstLean.Part291LocalEnergyBatch1
namespace BstLean.BlueprintLow
open Real Set BstLean.Part255
noncomputable def lowRectangle3_0 : FrameRectangleCertificate 9000 10000 (23/50) (921/2000) lowTIParameters0 where
  full := (101332968419/1000000000000)
  energy := (44267434443/62500000000)
  cov := (284485873111/1000000000000)
  schur := (524052538639/500000000000)
  cap := (220320677/250000000000)
  W2 := (3667179778951/1000000000000)
  V := (265679697/1000000000000)
  mass := (6746607/100000000000)
  rootN := (511885015721/500000000000)
  rootB := (5937281223/200000000000)
  rootU := (609595121969/1000000000000)
  rootV := (8149841977/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_0.scalar_checked
  centre := fun n hn => lowFull3_0 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy0 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_0.bound (by norm_num) hn lowTIParameters0_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_1 : FrameRectangleCertificate 9000 10000 (921/2000) (461/1000) lowTIParameters1 where
  full := (25352459889/250000000000)
  energy := (708032000171/1000000000000)
  cov := (142334083493/500000000000)
  schur := (523915351269/500000000000)
  cap := (220455513/250000000000)
  W2 := (3663839731819/1000000000000)
  V := (13292497/50000000000)
  mass := (61939317/1000000000000)
  rootN := (127954502567/125000000000)
  rootB := (29695488749/1000000000000)
  rootU := (304774260463/500000000000)
  rootV := (16304905397/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_1.scalar_checked
  centre := fun n hn => lowFull3_1 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy1 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_1.bound (by norm_num) hn lowTIParameters1_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_2 : FrameRectangleCertificate 9000 10000 (461/1000) (923/2000) lowTIParameters2 where
  full := (25371686659/250000000000)
  energy := (353892583027/500000000000)
  cov := (8901571031/31250000000)
  schur := (26188914843/25000000000)
  cap := (17647221/20000000000)
  W2 := (91512683277/25000000000)
  V := (33252501/125000000000)
  mass := (3558937/62500000000)
  rootN := (1023502121991/1000000000000)
  rootB := (29704562781/1000000000000)
  rootU := (609502239593/1000000000000)
  rootV := (4077529951/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_2.scalar_checked
  centre := fun n hn => lowFull3_2 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy2 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_2.bound (by norm_num) hn lowTIParameters2_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_3 : FrameRectangleCertificate 9000 10000 (923/2000) (231/500) lowTIParameters3 where
  full := (25390922581/250000000000)
  energy := (707538448651/1000000000000)
  cov := (11406326911/40000000000)
  schur := (4092755177/3906250000)
  cap := (220790459/250000000000)
  W2 := (114286954701/31250000000)
  V := (266307553/1000000000000)
  mass := (5242423/100000000000)
  rootN := (204718863353/200000000000)
  rootB := (29718038899/1000000000000)
  rootU := (609456278999/1000000000000)
  rootV := (16318932349/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_3.scalar_checked
  centre := fun n hn => lowFull3_3 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy3 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_3.bound (by norm_num) hn lowTIParameters3_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_4 : FrameRectangleCertificate 9000 10000 (231/500) (37/80) lowTIParameters4 where
  full := (101640671297/1000000000000)
  energy := (707291847877/1000000000000)
  cov := (285213920657/1000000000000)
  schur := (1047009165421/1000000000000)
  cap := (883438001/1000000000000)
  W2 := (1826932681879/500000000000)
  V := (4161869/15625000000)
  mass := (48335629/1000000000000)
  rootN := (255808664511/250000000000)
  rootB := (29722684957/1000000000000)
  rootU := (609410640211/1000000000000)
  rootV := (16320527443/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_4.scalar_checked
  centre := fun n hn => lowFull3_4 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy4 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_4.bound (by norm_num) hn lowTIParameters4_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_5 : FrameRectangleCertificate 9000 10000 (37/80) (463/1000) lowTIParameters5 where
  full := (158933891/1562500000)
  energy := (176761340913/250000000000)
  cov := (285521548207/1000000000000)
  schur := (1047197968771/1000000000000)
  cap := (442119141/500000000000)
  W2 := (3650555745107/1000000000000)
  V := (66661727/250000000000)
  mass := (5579333/125000000000)
  rootN := (40933076479/40000000000)
  rootB := (29736144371/1000000000000)
  rootU := (609365324321/1000000000000)
  rootV := (130634613/8000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_5.scalar_checked
  centre := fun n hn => lowFull3_5 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy5 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_5.bound (by norm_num) hn lowTIParameters5_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_6 : FrameRectangleCertificate 9000 10000 (463/1000) (927/2000) lowTIParameters6 where
  full := (50897373923/500000000000)
  energy := (44174937243/62500000000)
  cov := (285576818747/1000000000000)
  schur := (523231395389/500000000000)
  cap := (884513583/1000000000000)
  W2 := (1823626834277/500000000000)
  V := (66674631/250000000000)
  mass := (41283167/1000000000000)
  rootN := (204593527833/200000000000)
  rootB := (14870386537/500000000000)
  rootU := (609320332437/1000000000000)
  rootV := (8165453509/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_6.scalar_checked
  centre := fun n hn => lowFull3_6 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy6 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_6.bound (by norm_num) hn lowTIParameters6_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_7 : FrameRectangleCertificate 9000 10000 (927/2000) (58/125) lowTIParameters7 where
  full := (6366990301/62500000000)
  energy := (141310548901/200000000000)
  cov := (285884174429/1000000000000)
  schur := (26166291601/25000000000)
  cap := (442656683/500000000000)
  W2 := (91098977709/25000000000)
  V := (133492781/500000000000)
  mass := (9561717/250000000000)
  rootN := (1023059951343/1000000000000)
  rootB := (29754215937/1000000000000)
  rootU := (609275665691/1000000000000)
  rootV := (16339692837/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_7.scalar_checked
  centre := fun n hn => lowFull3_7 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy7 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_7.bound (by norm_num) hn lowTIParameters7_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_8 : FrameRectangleCertificate 9000 10000 (58/125) (929/2000) lowTIParameters8 where
  full := (50974490931/500000000000)
  energy := (35315330471/50000000000)
  cov := (4467796369/15625000000)
  schur := (522958729941/500000000000)
  cap := (442793903/500000000000)
  W2 := (1820336019473/500000000000)
  V := (267036733/1000000000000)
  mass := (1774749/50000000000)
  rootN := (1022701060859/1000000000000)
  rootB := (29758827363/1000000000000)
  rootU := (609231325249/1000000000000)
  rootV := (4085314653/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_8.scalar_checked
  centre := fun n hn => lowFull3_8 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy8 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_8.bound (by norm_num) hn lowTIParameters8_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_9 : FrameRectangleCertificate 9000 10000 (929/2000) (93/200) lowTIParameters9 where
  full := (12753269963/125000000000)
  energy := (353030295273/500000000000)
  cov := (286246051791/1000000000000)
  schur := (209221280249/200000000000)
  cap := (110798387/125000000000)
  W2 := (727478486939/200000000000)
  V := (267323517/1000000000000)
  mass := (4124979/125000000000)
  rootN := (1022793430389/1000000000000)
  rootB := (5954450759/200000000000)
  rootU := (121837462457/200000000000)
  rootV := (16350031101/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_9.scalar_checked
  centre := fun n hn => lowFull3_9 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy9 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_9.bound (by norm_num) hn lowTIParameters9_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_10 : FrameRectangleCertificate 9000 10000 (93/200) (931/2000) lowTIParameters10 where
  full := (10210337907/100000000000)
  energy := (705814687803/1000000000000)
  cov := (286300368049/1000000000000)
  schur := (209074632893/200000000000)
  cap := (221665171/250000000000)
  W2 := (908530067559/250000000000)
  V := (267374243/1000000000000)
  mass := (7684137/250000000000)
  rootN := (255608729857/250000000000)
  rootB := (29776848121/1000000000000)
  rootU := (121828725601/200000000000)
  rootV := (16351582279/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_10.scalar_checked
  centre := fun n hn => lowFull3_10 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy10 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_10.bound (by norm_num) hn lowTIParameters10_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_11 : FrameRectangleCertificate 9000 10000 (931/2000) (233/500) lowTIParameters11 where
  full := (1021806407/10000000000)
  energy := (705568901107/1000000000000)
  cov := (143303590539/500000000000)
  schur := (52278108607/50000000000)
  cap := (887459491/1000000000000)
  W2 := (1815427760157/500000000000)
  V := (133830387/500000000000)
  mass := (7170687/250000000000)
  rootN := (40901093817/40000000000)
  rootB := (7447564581/250000000000)
  rootU := (304550136823/500000000000)
  rootV := (16360341501/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_11.scalar_checked
  centre := fun n hn => lowFull3_11 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy11 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_11.bound (by norm_num) hn lowTIParameters11_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_12 : FrameRectangleCertificate 9000 10000 (233/500) (933/2000) lowTIParameters12 where
  full := (5112897267/50000000000)
  energy := (88165403797/125000000000)
  cov := (286661021301/1000000000000)
  schur := (208965979621/200000000000)
  cap := (887732233/1000000000000)
  W2 := (3627598159701/1000000000000)
  V := (53542211/200000000000)
  mass := (26818293/1000000000000)
  rootN := (1022169212071/1000000000000)
  rootB := (29794835677/1000000000000)
  rootU := (304528625227/500000000000)
  rootV := (8180939051/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_12.scalar_checked
  centre := fun n hn => lowFull3_12 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy12 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_12.bound (by norm_num) hn lowTIParameters12_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_13 : FrameRectangleCertificate 9000 10000 (933/2000) (467/1000) lowTIParameters13 where
  full := (102335293749/1000000000000)
  energy := (352538837763/500000000000)
  cov := (143483781773/500000000000)
  schur := (1045018970303/1000000000000)
  cap := (888530563/1000000000000)
  W2 := (3624348163367/1000000000000)
  V := (267997333/1000000000000)
  mass := (25125051/1000000000000)
  rootN := (20445233873/20000000000)
  rootB := (29808229787/1000000000000)
  rootU := (609014559717/1000000000000)
  rootV := (2046328011/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_13.scalar_checked
  centre := fun n hn => lowFull3_13 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy13 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_13.bound (by norm_num) hn lowTIParameters13_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_14 : FrameRectangleCertificate 9000 10000 (467/1000) (187/400) lowTIParameters14 where
  full := (25603171673/250000000000)
  energy := (704832236477/1000000000000)
  cov := (143510464299/500000000000)
  schur := (208857530859/200000000000)
  cap := (222200617/250000000000)
  W2 := (3621105506399/1000000000000)
  V := (26804717/100000000000)
  mass := (23586691/1000000000000)
  rootN := (1021903935943/1000000000000)
  rootB := (29812790343/1000000000000)
  rootU := (608972202737/1000000000000)
  rootV := (4093036541/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_14.scalar_checked
  centre := fun n hn => lowFull3_14 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy14 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_14.bound (by norm_num) hn lowTIParameters14_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_15 : FrameRectangleCertificate 9000 10000 (187/400) (117/250) lowTIParameters15 where
  full := (102490124947/1000000000000)
  energy := (88073364143/125000000000)
  cov := (287327200417/1000000000000)
  schur := (1044476789273/1000000000000)
  cap := (88960033/100000000000)
  W2 := (56529221311/15625000000)
  V := (67083299/250000000000)
  mass := (1386781/62500000000)
  rootN := (1021996472241/1000000000000)
  rootB := (932067767/31250000000)
  rootU := (608930180843/1000000000000)
  rootV := (127975617/7812500000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_15.scalar_checked
  centre := fun n hn => lowFull3_15 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy15 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_15.bound (by norm_num) hn lowTIParameters15_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_16 : FrameRectangleCertificate 9000 10000 (117/250) (937/2000) lowTIParameters16 where
  full := (102567609297/1000000000000)
  energy := (140868341089/200000000000)
  cov := (143690045357/500000000000)
  schur := (1043746424969/1000000000000)
  cap := (444935703/500000000000)
  W2 := (3614642111169/1000000000000)
  V := (26838259/100000000000)
  mass := (20917199/1000000000000)
  rootN := (1021639087433/1000000000000)
  rootB := (29830712463/1000000000000)
  rootU := (608888495381/1000000000000)
  rootV := (16382386579/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_16.scalar_checked
  centre := fun n hn => lowFull3_16 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy16 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_16.bound (by norm_num) hn lowTIParameters16_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_17 : FrameRectangleCertificate 9000 10000 (937/2000) (469/1000) lowTIParameters17 where
  full := (102645140539/1000000000000)
  energy := (704096613301/1000000000000)
  cov := (143843046233/500000000000)
  schur := (1043935621003/1000000000000)
  cap := (445334403/500000000000)
  W2 := (1805710661817/500000000000)
  V := (268668363/1000000000000)
  mass := (9880419/500000000000)
  rootN := (255432919399/250000000000)
  rootB := (2984407489/100000000000)
  rootU := (30442357387/50000000000)
  rootV := (16391106217/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_17.scalar_checked
  centre := fun n hn => lowFull3_17 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy17 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_17.bound (by norm_num) hn lowTIParameters17_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_18 : FrameRectangleCertificate 9000 10000 (469/1000) (939/2000) lowTIParameters18 where
  full := (102722719479/1000000000000)
  energy := (703851636627/1000000000000)
  cov := (287738508859/1000000000000)
  schur := (1043206203751/1000000000000)
  cap := (445469531/500000000000)
  W2 := (1804103888371/500000000000)
  V := (134358657/500000000000)
  mass := (18708617/1000000000000)
  rootN := (1021374663751/1000000000000)
  rootB := (14924301173/500000000000)
  rootU := (608806139319/1000000000000)
  rootV := (16392599367/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_18.scalar_checked
  centre := fun n hn => lowFull3_18 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy18 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_18.bound (by norm_num) hn lowTIParameters18_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_19 : FrameRectangleCertificate 9000 10000 (939/2000) (47/100) lowTIParameters19 where
  full := (102800346931/1000000000000)
  energy := (351803387671/500000000000)
  cov := (288044240899/1000000000000)
  schur := (260848864777/250000000000)
  cap := (891736007/1000000000000)
  W2 := (3605001446173/1000000000000)
  V := (67250709/250000000000)
  mass := (17750793/1000000000000)
  rootN := (1021467306921/1000000000000)
  rootB := (597238983/20000000000)
  rootU := (9511960493/15625000000)
  rootV := (4100326481/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_19.scalar_checked
  centre := fun n hn => lowFull3_19 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy19 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_19.bound (by norm_num) hn lowTIParameters19_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_20 : FrameRectangleCertificate 9000 10000 (47/100) (941/2000) lowTIParameters20 where
  full := (51439011861/500000000000)
  energy := (703362029363/1000000000000)
  cov := (144048091891/500000000000)
  schur := (8341335861/8000000000)
  cap := (892005451/1000000000000)
  W2 := (1800901153783/500000000000)
  V := (53810269/200000000000)
  mass := (2109821/125000000000)
  rootN := (1021110661303/1000000000000)
  rootB := (29866460303/1000000000000)
  rootU := (608725145891/1000000000000)
  rootV := (16402784673/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_20.scalar_checked
  centre := fun n hn => lowFull3_20 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy20 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_20.bound (by norm_num) hn lowTIParameters20_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_21 : FrameRectangleCertificate 9000 10000 (941/2000) (471/1000) lowTIParameters21 where
  full := (51477875343/500000000000)
  energy := (175779349653/250000000000)
  cov := (72100411617/250000000000)
  schur := (1042856295629/1000000000000)
  cap := (17856039/20000000000)
  W2 := (719722067373/200000000000)
  V := (134668307/500000000000)
  mass := (3216799/200000000000)
  rootN := (127650419581/125000000000)
  rootB := (14939895833/500000000000)
  rootU := (38042822739/62500000000)
  rootV := (8205739059/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_21.scalar_checked
  centre := fun n hn => lowFull3_21 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy21 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_21.bound (by norm_num) hn lowTIParameters21_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_22 : FrameRectangleCertificate 9000 10000 (471/1000) (943/2000) lowTIParameters22 where
  full := (103033528669/1000000000000)
  energy := (702872883003/1000000000000)
  cov := (288707109409/1000000000000)
  schur := (521522860287/500000000000)
  cap := (893598489/1000000000000)
  W2 := (35954255099/10000000000)
  V := (53924377/200000000000)
  mass := (15359891/1000000000000)
  rootN := (63831006149/62500000000)
  rootB := (14946558877/500000000000)
  rootU := (9510086357/15625000000)
  rootV := (8210083511/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_22.scalar_checked
  centre := fun n hn => lowFull3_22 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy22 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_22.bound (by norm_num) hn lowTIParameters22_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_23 : FrameRectangleCertificate 9000 10000 (943/2000) (59/125) lowTIParameters23 where
  full := (103111358529/1000000000000)
  energy := (702628482457/1000000000000)
  cov := (289012572603/1000000000000)
  schur := (1043235257087/1000000000000)
  cap := (178879013/200000000000)
  W2 := (718449560553/200000000000)
  V := (53981431/200000000000)
  mass := (14699763/1000000000000)
  rootN := (204277777263/200000000000)
  rootB := (29906438521/1000000000000)
  rootU := (152151559127/250000000000)
  rootV := (16428851299/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_23.scalar_checked
  centre := fun n hn => lowFull3_23 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy23 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_23.bound (by norm_num) hn lowTIParameters23_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_24 : FrameRectangleCertificate 9000 10000 (59/125) (189/400) lowTIParameters24 where
  full := (25797310283/250000000000)
  energy := (140476839379/200000000000)
  cov := (289318036049/1000000000000)
  schur := (521712452407/500000000000)
  cap := (895191681/1000000000000)
  W2 := (3589077191679/1000000000000)
  V := (10807697/40000000000)
  mass := (7048869/500000000000)
  rootN := (204296344051/200000000000)
  rootB := (29919754027/1000000000000)
  rootU := (19017727949/31250000000)
  rootV := (16437530989/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_24.scalar_checked
  centre := fun n hn => lowFull3_24 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy24 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_24.bound (by norm_num) hn lowTIParameters24_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_25 : FrameRectangleCertificate 9000 10000 (189/400) (473/1000) lowTIParameters25 where
  full := (51633588677/500000000000)
  energy := (351070013117/500000000000)
  cov := (72405874937/250000000000)
  schur := (104361466337/100000000000)
  cap := (44799417/50000000000)
  W2 := (3585913652837/1000000000000)
  V := (2113107/7812500000)
  mass := (13548503/1000000000000)
  rootN := (1021574600003/1000000000000)
  rootB := (29933064327/1000000000000)
  rootU := (121705740401/200000000000)
  rootV := (1027887883/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_25.scalar_checked
  centre := fun n hn => lowFull3_25 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy25 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_25.bound (by norm_num) hn lowTIParameters25_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_26 : FrameRectangleCertificate 9000 10000 (473/1000) (947/2000) lowTIParameters26 where
  full := (103345168083/1000000000000)
  energy := (350947985197/500000000000)
  cov := (2899289637/10000000000)
  schur := (208760906481/200000000000)
  cap := (179357009/200000000000)
  W2 := (71655143253/20000000000)
  V := (270762967/1000000000000)
  mass := (815453/62500000000)
  rootN := (8173340203/8000000000)
  rootB := (748659237/25000000000)
  rootU := (608490461039/1000000000000)
  rootV := (8227438347/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_26.scalar_checked
  centre := fun n hn => lowFull3_26 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy26 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_26.bound (by norm_num) hn lowTIParameters26_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_27 : FrameRectangleCertificate 9000 10000 (947/2000) (237/500) lowTIParameters27 where
  full := (51711607109/500000000000)
  energy := (701652029291/1000000000000)
  cov := (145117213953/500000000000)
  schur := (521997255767/500000000000)
  cap := (224395449/250000000000)
  W2 := (3579607697543/1000000000000)
  V := (135524119/500000000000)
  mass := (6294809/500000000000)
  rootN := (1021760496171/1000000000000)
  rootB := (29959669491/1000000000000)
  rootU := (608452573107/1000000000000)
  rootV := (16463542693/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_27.scalar_checked
  centre := fun n hn => lowFull3_27 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy27 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_27.bound (by norm_num) hn lowTIParameters27_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_28 : FrameRectangleCertificate 9000 10000 (237/500) (949/2000) lowTIParameters28 where
  full := (103501316669/1000000000000)
  energy := (701408202847/1000000000000)
  cov := (290539892361/1000000000000)
  schur := (1044184600387/1000000000000)
  cap := (179675719/200000000000)
  W2 := (715293046823/200000000000)
  V := (27133351/100000000000)
  mass := (12171667/1000000000000)
  rootN := (255463378049/250000000000)
  rootB := (14986482201/500000000000)
  rootU := (15210375997/25000000000)
  rootV := (4118051041/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_28.scalar_checked
  centre := fun n hn => lowFull3_28 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy28 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_28.bound (by norm_num) hn lowTIParameters28_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_29 : FrameRectangleCertificate 9000 10000 (949/2000) (19/40) lowTIParameters29 where
  full := (103579476357/1000000000000)
  energy := (87645561373/125000000000)
  cov := (290845357069/1000000000000)
  schur := (130546849829/125000000000)
  cap := (179835089/200000000000)
  W2 := (446666218641/125000000000)
  V := (135809391/500000000000)
  mass := (11789821/1000000000000)
  rootN := (1021946573277/1000000000000)
  rootB := (7496563567/250000000000)
  rootU := (76047232883/125000000000)
  rootV := (8240430541/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_29.scalar_checked
  centre := fun n hn => lowFull3_29 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy29 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_29.bound (by norm_num) hn lowTIParameters29_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_30 : FrameRectangleCertificate 9000 10000 (19/40) (951/2000) lowTIParameters30 where
  full := (103657694211/1000000000000)
  energy := (350460446809/500000000000)
  cov := (72787705507/250000000000)
  schur := (1044565105891/1000000000000)
  cap := (224993087/250000000000)
  W2 := (35702012193/10000000000)
  V := (135952027/500000000000)
  mass := (11440839/1000000000000)
  rootN := (63877479951/62500000000)
  rootB := (2999953913/100000000000)
  rootU := (38021315273/62500000000)
  rootV := (1030594591/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_30.scalar_checked
  centre := fun n hn => lowFull3_30 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy30 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_30.bound (by norm_num) hn lowTIParameters30_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_31 : FrameRectangleCertificate 9000 10000 (951/2000) (119/250) lowTIParameters31 where
  full := (4149438847/40000000000)
  energy := (700677410671/1000000000000)
  cov := (72864071809/250000000000)
  schur := (208951104361/200000000000)
  cap := (180153861/200000000000)
  W2 := (1783539810789/500000000000)
  V := (136094663/500000000000)
  mass := (11121781/1000000000000)
  rootN := (40885313193/40000000000)
  rootB := (7503204753/250000000000)
  rootU := (38019036597/62500000000)
  rootV := (4124540323/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_31.scalar_checked
  centre := fun n hn => lowFull3_31 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy31 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_31.bound (by norm_num) hn lowTIParameters31_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_32 : FrameRectangleCertificate 9000 10000 (119/250) (953/2000) lowTIParameters32 where
  full := (25953577051/250000000000)
  energy := (350217021031/500000000000)
  cov := (145880876347/500000000000)
  schur := (1044946046011/1000000000000)
  cap := (450783159/500000000000)
  W2 := (445495616613/125000000000)
  V := (136237299/500000000000)
  mass := (10829981/1000000000000)
  rootN := (511113012457/500000000000)
  rootB := (234578859/7812500000)
  rootU := (304134244197/500000000000)
  rootV := (16506804597/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_32.scalar_checked
  centre := fun n hn => lowFull3_32 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy32 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_32.bound (by norm_num) hn lowTIParameters32_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_33 : FrameRectangleCertificate 9000 10000 (953/2000) (477/1000) lowTIParameters33 where
  full := (51946353131/500000000000)
  energy := (700190787709/1000000000000)
  cov := (146033609201/500000000000)
  schur := (1045136678159/1000000000000)
  cap := (90236339/100000000000)
  W2 := (1780428565193/500000000000)
  V := (272759871/1000000000000)
  mass := (10563019/1000000000000)
  rootN := (1022319264301/1000000000000)
  rootB := (3754920501/125000000000)
  rootU := (608232754699/1000000000000)
  rootV := (1651544341/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_33.scalar_checked
  centre := fun n hn => lowFull3_33 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy33 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_33.bound (by norm_num) hn lowTIParameters33_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_34 : FrameRectangleCertificate 9000 10000 (477/1000) (191/400) lowTIParameters34 where
  full := (4158846653/40000000000)
  energy := (349973823769/500000000000)
  cov := (146186342179/500000000000)
  schur := (1045327417899/1000000000000)
  cap := (903160521/1000000000000)
  W2 := (3557756191277/1000000000000)
  V := (34130643/125000000000)
  mass := (5159349/500000000000)
  rootN := (1022412547801/1000000000000)
  rootB := (30052629187/1000000000000)
  rootU := (121639477261/200000000000)
  rootV := (3304815541/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_34.scalar_checked
  centre := fun n hn => lowFull3_34 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy34 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_34.bound (by norm_num) hn lowTIParameters34_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_35 : FrameRectangleCertificate 9000 10000 (191/400) (239/500) lowTIParameters35 where
  full := (104049689383/1000000000000)
  energy := (349852310731/500000000000)
  cov := (58535630113/200000000000)
  schur := (522759132439/500000000000)
  cap := (451978859/500000000000)
  W2 := (1777331046409/500000000000)
  V := (273330417/1000000000000)
  mass := (5047511/500000000000)
  rootN := (102250587523/100000000000)
  rootB := (3006588961/100000000000)
  rootU := (24326495403/40000000000)
  rootV := (4133176873/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_35.scalar_checked
  centre := fun n hn => lowFull3_35 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy35 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_35.bound (by norm_num) hn lowTIParameters35_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_36 : FrameRectangleCertificate 9000 10000 (239/500) (957/2000) lowTIParameters36 where
  full := (20825655287/200000000000)
  energy := (699461709407/1000000000000)
  cov := (146491808509/500000000000)
  schur := (522854609371/500000000000)
  cap := (28273593/31250000000)
  W2 := (1775787406231/500000000000)
  V := (27361569/100000000000)
  mass := (9890179/1000000000000)
  rootN := (1022599246403/1000000000000)
  rootB := (30079145201/1000000000000)
  rootU := (76015969113/125000000000)
  rootV := (2067666597/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_36.scalar_checked
  centre := fun n hn => lowFull3_36 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy36 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_36.bound (by norm_num) hn lowTIParameters36_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_37 : FrameRectangleCertificate 9000 10000 (957/2000) (479/1000) lowTIParameters37 where
  full := (52103464247/500000000000)
  energy := (699218911291/1000000000000)
  cov := (293289083717/1000000000000)
  schur := (1045900279131/1000000000000)
  cap := (56597019/62500000000)
  W2 := (1774247163847/500000000000)
  V := (68475241/250000000000)
  mass := (9702519/1000000000000)
  rootN := (1022692661131/1000000000000)
  rootB := (7523099029/250000000000)
  rootU := (608093491717/1000000000000)
  rootV := (4137488399/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_37.scalar_checked
  centre := fun n hn => lowFull3_37 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy37 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_37.bound (by norm_num) hn lowTIParameters37_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_38 : FrameRectangleCertificate 9000 10000 (479/1000) (959/2000) lowTIParameters38 where
  full := (52142823291/500000000000)
  energy := (349488113519/500000000000)
  cov := (146797275333/500000000000)
  schur := (52304572287/50000000000)
  cap := (453174849/500000000000)
  W2 := (3545420616161/1000000000000)
  V := (274186237/1000000000000)
  mass := (4765273/500000000000)
  rootN := (204557223851/200000000000)
  rootB := (3763205287/125000000000)
  rootU := (304029801731/500000000000)
  rootV := (2069821237/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_38.scalar_checked
  centre := fun n hn => lowFull3_38 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy38 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_38.bound (by norm_num) hn lowTIParameters38_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_39 : FrameRectangleCertificate 9000 10000 (959/2000) (12/25) lowTIParameters39 where
  full := (13045553967/125000000000)
  energy := (139746731313/200000000000)
  cov := (293900017861/1000000000000)
  schur := (130785339773/125000000000)
  cap := (907147167/1000000000000)
  W2 := (221397103469/62500000000)
  V := (274471511/1000000000000)
  mass := (292903/31250000000)
  rootN := (511439810287/500000000000)
  rootB := (15059441947/500000000000)
  rootU := (608026090119/1000000000000)
  rootV := (8283590873/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_39.scalar_checked
  centre := fun n hn => lowFull3_39 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy39 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_39.bound (by norm_num) hn lowTIParameters39_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_40 : FrameRectangleCertificate 9000 10000 (12/25) (961/2000) lowTIParameters40 where
  full := (104443285003/1000000000000)
  energy := (698491199793/1000000000000)
  cov := (291632286603/1000000000000)
  schur := (207465661769/200000000000)
  cap := (902603511/1000000000000)
  W2 := (1769646711761/500000000000)
  V := (27235369/100000000000)
  mass := (922833/100000000000)
  rootN := (1018493156013/1000000000000)
  rootB := (6008672103/200000000000)
  rootU := (121598590739/200000000000)
  rootV := (16503141823/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_40.scalar_checked
  centre := fun n hn => lowFull3_40 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy40 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_40.bound (by norm_num) hn lowTIParameters40_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_41 : FrameRectangleCertificate 9000 10000 (961/2000) (481/1000) lowTIParameters41 where
  full := (52261103721/500000000000)
  energy := (698248856647/1000000000000)
  cov := (291935075027/1000000000000)
  schur := (259379527277/250000000000)
  cap := (112924503/125000000000)
  W2 := (1768119949077/500000000000)
  V := (272636463/1000000000000)
  mass := (4547859/500000000000)
  rootN := (509293164373/500000000000)
  rootB := (7514136777/250000000000)
  rootU := (60796019623/100000000000)
  rootV := (16511706847/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_41.scalar_checked
  centre := fun n hn => lowFull3_41 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy41 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_41.bound (by norm_num) hn lowTIParameters41_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_42 : FrameRectangleCertificate 9000 10000 (481/1000) (963/2000) lowTIParameters42 where
  full := (104601200129/1000000000000)
  energy := (349003313523/500000000000)
  cov := (18264866481/62500000000)
  schur := (207541602659/200000000000)
  cap := (452094307/500000000000)
  W2 := (441649132177/125000000000)
  V := (54583847/200000000000)
  mass := (8974033/1000000000000)
  rootN := (1018679543967/1000000000000)
  rootB := (15034864599/500000000000)
  rootU := (303963909903/500000000000)
  rootV := (16520267401/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_42.scalar_checked
  centre := fun n hn => lowFull3_42 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy42 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_42.bound (by norm_num) hn lowTIParameters42_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_43 : FrameRectangleCertificate 9000 10000 (963/2000) (241/500) lowTIParameters43 where
  full := (20936052829/200000000000)
  energy := (697764510909/1000000000000)
  cov := (58508130521/200000000000)
  schur := (51894901051/50000000000)
  cap := (452490643/500000000000)
  W2 := (220634554957/62500000000)
  V := (34150251/125000000000)
  mass := (443117/50000000000)
  rootN := (1018772801473/1000000000000)
  rootB := (48132651/1600000000)
  rootU := (607895826503/1000000000000)
  rootV := (64565717/3906250000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_43.scalar_checked
  centre := fun n hn => lowFull3_43 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy43 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_43.bound (by norm_num) hn lowTIParameters43_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_44 : FrameRectangleCertificate 9000 10000 (241/500) (193/400) lowTIParameters44 where
  full := (10475940059/100000000000)
  energy := (348761254081/500000000000)
  cov := (292843441759/1000000000000)
  schur := (129761016501/125000000000)
  cap := (905774041/1000000000000)
  W2 := (3527119342131/1000000000000)
  V := (273484781/1000000000000)
  mass := (4379893/500000000000)
  rootN := (1018866101119/1000000000000)
  rootB := (30096080161/1000000000000)
  rootU := (303932109233/500000000000)
  rootV := (4134343819/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_44.scalar_checked
  centre := fun n hn => lowFull3_44 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy44 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_44.bound (by norm_num) hn lowTIParameters44_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_45 : FrameRectangleCertificate 9000 10000 (193/400) (483/1000) lowTIParameters45 where
  full := (26209652643/250000000000)
  energy := (174320154681/250000000000)
  cov := (146573115577/500000000000)
  schur := (519139172943/500000000000)
  cap := (906566881/1000000000000)
  W2 := (3524092424111/1000000000000)
  V := (136883777/500000000000)
  mass := (1083199/125000000000)
  rootN := (101895944271/100000000000)
  rootB := (15054624547/500000000000)
  rootU := (607832997847/1000000000000)
  rootV := (827296129/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_45.scalar_checked
  centre := fun n hn => lowFull3_45 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy45 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_45.bound (by norm_num) hn lowTIParameters45_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_46 : FrameRectangleCertificate 9000 10000 (483/1000) (967/2000) lowTIParameters46 where
  full := (6557368451/62500000000)
  energy := (348519421259/500000000000)
  cov := (29344902079/100000000000)
  schur := (129808582793/125000000000)
  cap := (90735981/100000000000)
  W2 := (704214420733/200000000000)
  V := (34256291/125000000000)
  mass := (2144763/250000000000)
  rootN := (509526413041/500000000000)
  rootB := (7530603437/250000000000)
  rootU := (121560433369/200000000000)
  rootV := (16554465501/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_46.scalar_checked
  centre := fun n hn => lowFull3_46 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy46 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_46.bound (by norm_num) hn lowTIParameters46_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_47 : FrameRectangleCertificate 9000 10000 (967/2000) (121/250) lowTIParameters47 where
  full := (13124656957/125000000000)
  energy := (87099647433/125000000000)
  cov := (293751810667/1000000000000)
  schur := (1038659081033/1000000000000)
  cap := (90815283/100000000000)
  W2 := (4397572949/1250000000)
  V := (137166551/500000000000)
  mass := (8499517/1000000000000)
  rootN := (254786562763/250000000000)
  rootB := (30135574161/1000000000000)
  rootU := (607771727669/1000000000000)
  rootV := (3312600803/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_47.scalar_checked
  centre := fun n hn => lowFull3_47 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy47 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_47.bound (by norm_num) hn lowTIParameters47_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_48 : FrameRectangleCertificate 9000 10000 (121/250) (969/2000) lowTIParameters48 where
  full := (52538346521/500000000000)
  energy := (348277814743/500000000000)
  cov := (18378412549/62500000000)
  schur := (64928100103/62500000000)
  cap := (45447297/50000000000)
  W2 := (3515051169357/1000000000000)
  V := (68653969/250000000000)
  mass := (10533/1250000000)
  rootN := (1019239717461/1000000000000)
  rootB := (15074365161/500000000000)
  rootU := (75967710323/125000000000)
  rootV := (16571538131/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_48.scalar_checked
  centre := fun n hn => lowFull3_48 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy48 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_48.bound (by norm_num) hn lowTIParameters48_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_49 : FrameRectangleCertificate 9000 10000 (969/2000) (97/200) lowTIParameters49 where
  full := (21031241707/200000000000)
  energy := (348157096253/500000000000)
  cov := (294357391143/1000000000000)
  schur := (1039040223861/1000000000000)
  cap := (909739147/1000000000000)
  W2 := (3512050512787/1000000000000)
  V := (5497973/20000000000)
  mass := (8359161/1000000000000)
  rootN := (509666612567/500000000000)
  rootB := (1885117647/62500000000)
  rootU := (607712033869/1000000000000)
  rootV := (16580067853/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_49.scalar_checked
  centre := fun n hn => lowFull3_49 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy49 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_49.bound (by norm_num) hn lowTIParameters49_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_50 : FrameRectangleCertificate 9000 10000 (97/200) (971/2000) lowTIParameters50 where
  full := (10523580331/100000000000)
  energy := (139214573689/200000000000)
  cov := (294660181739/1000000000000)
  schur := (103923094733/100000000000)
  cap := (910532449/1000000000000)
  W2 := (3509056368217/1000000000000)
  V := (17198839/62500000000)
  mass := (8297309/1000000000000)
  rootN := (509713386947/500000000000)
  rootB := (1885939389/62500000000)
  rootU := (121536556767/200000000000)
  rootV := (1658859319/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_50.scalar_checked
  centre := fun n hn => lowFull3_50 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy50 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_50.bound (by norm_num) hn lowTIParameters50_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_51 : FrameRectangleCertificate 9000 10000 (971/2000) (243/500) lowTIParameters51 where
  full := (26328869639/250000000000)
  energy := (695831657229/1000000000000)
  cov := (9217592893/31250000000)
  schur := (1039421771759/1000000000000)
  cap := (911325853/1000000000000)
  W2 := (3506068714543/1000000000000)
  V := (275464199/1000000000000)
  mass := (2060099/250000000000)
  rootN := (1019520363583/1000000000000)
  rootB := (30188174059/1000000000000)
  rootU := (607653934837/1000000000000)
  rootV := (16597114177/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_51.scalar_checked
  centre := fun n hn => lowFull3_51 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy51 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_51.bound (by norm_num) hn lowTIParameters51_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_52 : FrameRectangleCertificate 9000 10000 (243/500) (973/2000) lowTIParameters52 where
  full := (4215809419/40000000000)
  energy := (86948819847/125000000000)
  cov := (295265763651/1000000000000)
  schur := (519806348403/500000000000)
  cap := (912119359/1000000000000)
  W2 := (875771882663/250000000000)
  V := (275746973/1000000000000)
  mass := (8188011/1000000000000)
  rootN := (1019613994023/1000000000000)
  rootB := (30201313863/1000000000000)
  rootU := (607625489247/1000000000000)
  rootV := (8302815381/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_52.scalar_checked
  centre := fun n hn => lowFull3_52 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy52 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_52.bound (by norm_num) hn lowTIParameters52_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_53 : FrameRectangleCertificate 9000 10000 (973/2000) (487/1000) lowTIParameters53 where
  full := (52737537641/500000000000)
  energy := (69534957301/100000000000)
  cov := (147784277483/500000000000)
  schur := (12997546527/12500000000)
  cap := (912912971/1000000000000)
  W2 := (1750056397801/500000000000)
  V := (276029749/1000000000000)
  mass := (406989/50000000000)
  rootN := (20394153301/20000000000)
  rootB := (15107224853/500000000000)
  rootU := (303798724739/500000000000)
  rootV := (8307071521/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_53.scalar_checked
  centre := fun n hn => lowFull3_53 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy53 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_53.bound (by norm_num) hn lowTIParameters53_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_54 : FrameRectangleCertificate 9000 10000 (487/1000) (39/80) lowTIParameters54 where
  full := (105554999207/1000000000000)
  energy := (43444293741/62500000000)
  cov := (147935673259/500000000000)
  schur := (207998969503/200000000000)
  cap := (91370669/100000000000)
  W2 := (1748572244271/500000000000)
  V := (69078131/250000000000)
  mass := (12649/1562500000)
  rootN := (509900688251/500000000000)
  rootB := (30227581611/1000000000000)
  rootU := (75946227247/125000000000)
  rootV := (4155662733/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_54.scalar_checked
  centre := fun n hn => lowFull3_54 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy54 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_54.bound (by norm_num) hn lowTIParameters54_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_55 : FrameRectangleCertificate 9000 10000 (39/80) (61/125) lowTIParameters55 where
  full := (105635008493/1000000000000)
  energy := (694867939233/1000000000000)
  cov := (296174138309/1000000000000)
  schur := (1040186072529/1000000000000)
  cap := (914500519/1000000000000)
  W2 := (3494182588629/1000000000000)
  V := (276595299/1000000000000)
  mass := (8054439/1000000000000)
  rootN := (509947564101/500000000000)
  rootB := (29531943/976562500)
  rootU := (151885649303/250000000000)
  rootV := (1663115447/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_55.scalar_checked
  centre := fun n hn => lowFull3_55 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy55 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_55.bound (by norm_num) hn lowTIParameters55_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_56 : FrameRectangleCertificate 9000 10000 (61/125) (977/2000) lowTIParameters56 where
  full := (21143020879/200000000000)
  energy := (173656822767/250000000000)
  cov := (9264904073/31250000000)
  schur := (1040377396903/1000000000000)
  cap := (45764723/50000000000)
  W2 := (3491227075211/1000000000000)
  V := (11075123/40000000000)
  mass := (801673/100000000000)
  rootN := (1019988919991/1000000000000)
  rootB := (30253833807/1000000000000)
  rootU := (60751578969/100000000000)
  rootV := (16639653693/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_56.scalar_checked
  centre := fun n hn => lowFull3_56 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy56 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_56.bound (by norm_num) hn lowTIParameters56_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_57 : FrameRectangleCertificate 9000 10000 (977/2000) (489/1000) lowTIParameters57 where
  full := (52897644093/500000000000)
  energy := (8679834441/12500000000)
  cov := (148389861299/500000000000)
  schur := (208113764063/200000000000)
  cap := (916088517/1000000000000)
  W2 := (3488277927663/1000000000000)
  V := (277160851/1000000000000)
  mass := (798197/100000000000)
  rootN := (10200827517/10000000000)
  rootB := (945842319/31250000000)
  rootU := (607489397957/1000000000000)
  rootV := (520254643/31250000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_57.scalar_checked
  centre := fun n hn => lowFull3_57 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy57 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_57.bound (by norm_num) hn lowTIParameters57_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_58 : FrameRectangleCertificate 9000 10000 (489/1000) (979/2000) lowTIParameters58 where
  full := (1654305643/15625000000)
  energy := (694146331799/1000000000000)
  cov := (37135314387/125000000000)
  schur := (104076034247/100000000000)
  cap := (458441347/500000000000)
  W2 := (348533512553/100000000000)
  V := (277443627/1000000000000)
  mass := (49687/6250000000)
  rootN := (510088311587/500000000000)
  rootB := (6056014181/200000000000)
  rootU := (303731712297/500000000000)
  rootV := (16656639127/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_58.scalar_checked
  centre := fun n hn => lowFull3_58 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy58 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_58.bound (by norm_num) hn lowTIParameters58_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_59 : FrameRectangleCertificate 9000 10000 (979/2000) (49/100) lowTIParameters59 where
  full := (10595592459/100000000000)
  energy := (346953010271/500000000000)
  cov := (297385307833/1000000000000)
  schur := (1040951963063/1000000000000)
  cap := (917676991/1000000000000)
  W2 := (3482398648323/1000000000000)
  V := (277726403/1000000000000)
  mass := (198009/25000000000)
  rootN := (1020270534253/1000000000000)
  rootB := (946661997/31250000000)
  rootU := (607437872193/1000000000000)
  rootV := (16665125353/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_59.scalar_checked
  centre := fun n hn => lowFull3_59 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy59 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_59.bound (by norm_num) hn lowTIParameters59_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_60 : FrameRectangleCertificate 9000 10000 (49/100) (981/2000) lowTIParameters60 where
  full := (13254547477/125000000000)
  energy := (173416455359/250000000000)
  cov := (73773794117/250000000000)
  schur := (8256659261/8000000000)
  cap := (28534229/31250000000)
  W2 := (34794684757/10000000000)
  V := (275587663/1000000000000)
  mass := (789309/100000000000)
  rootN := (101591456709/100000000000)
  rootB := (30217467267/1000000000000)
  rootU := (303706371701/500000000000)
  rootV := (8300416601/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_60.scalar_checked
  centre := fun n hn => lowFull3_60 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy60 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_60.bound (by norm_num) hn lowTIParameters60_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_61 : FrameRectangleCertificate 9000 10000 (981/2000) (491/1000) lowTIParameters61 where
  full := (26529232039/250000000000)
  energy := (346712867201/500000000000)
  cov := (36924415613/125000000000)
  schur := (1032272545421/1000000000000)
  cap := (228471211/250000000000)
  W2 := (3476544587427/1000000000000)
  V := (27586797/100000000000)
  mass := (1966981/250000000000)
  rootN := (1016008142399/1000000000000)
  rootB := (6046105669/200000000000)
  rootU := (60738804089/100000000000)
  rootV := (3321854723/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_61.scalar_checked
  centre := fun n hn => lowFull3_61 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy61 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_61.bound (by norm_num) hn lowTIParameters61_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_62 : FrameRectangleCertificate 9000 10000 (491/1000) (983/2000) lowTIParameters62 where
  full := (21239514191/200000000000)
  energy := (693185759367/1000000000000)
  cov := (73923868393/250000000000)
  schur := (1032462779879/1000000000000)
  cap := (228668623/250000000000)
  W2 := (217101685211/62500000000)
  V := (276148277/1000000000000)
  mass := (7844693/1000000000000)
  rootN := (63506359791/62500000000)
  rootB := (6048717193/200000000000)
  rootU := (607363767371/1000000000000)
  rootV := (830885487/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_62.scalar_checked
  centre := fun n hn => lowFull3_62 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy62 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_62.bound (by norm_num) hn lowTIParameters62_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_63 : FrameRectangleCertificate 9000 10000 (983/2000) (123/250) lowTIParameters63 where
  full := (26569577393/250000000000)
  energy := (346472948127/500000000000)
  cov := (295995622473/1000000000000)
  schur := (32270409709/31250000000)
  cap := (91546427/100000000000)
  W2 := (3470715583423/1000000000000)
  V := (34553573/125000000000)
  mass := (1955811/250000000000)
  rootN := (1016195409697/1000000000000)
  rootB := (15128320049/500000000000)
  rootU := (607339925587/1000000000000)
  rootV := (3325228317/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_63.scalar_checked
  centre := fun n hn => lowFull3_63 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy63 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_63.bound (by norm_num) hn lowTIParameters63_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_64 : FrameRectangleCertificate 9000 10000 (123/250) (197/400) lowTIParameters64 where
  full := (106359145377/1000000000000)
  energy := (346353072493/500000000000)
  cov := (59259154321/200000000000)
  schur := (1032843537549/1000000000000)
  cap := (458127093/500000000000)
  W2 := (3467810427593/1000000000000)
  V := (69177223/250000000000)
  mass := (7803433/1000000000000)
  rootN := (1016289101363/1000000000000)
  rootB := (30269690881/1000000000000)
  rootU := (607316518307/1000000000000)
  rootV := (8317284593/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_64.scalar_checked
  centre := fun n hn => lowFull3_64 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy64 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_64.bound (by norm_num) hn lowTIParameters64_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_65 : FrameRectangleCertificate 9000 10000 (197/400) (493/1000) lowTIParameters65 where
  full := (1330500997/12500000000)
  energy := (346233252743/500000000000)
  cov := (296595920969/1000000000000)
  schur := (516517030079/500000000000)
  cap := (11463053/12500000000)
  W2 := (3464911475951/1000000000000)
  V := (692473/2500000000)
  mass := (7785131/1000000000000)
  rootN := (127047853937/125000000000)
  rootB := (15141369159/500000000000)
  rootU := (303646774173/500000000000)
  rootV := (416074813/25000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_65.scalar_checked
  centre := fun n hn => lowFull3_65 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy65 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_65.bound (by norm_num) hn lowTIParameters65_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_66 : FrameRectangleCertificate 9000 10000 (493/1000) (987/2000) lowTIParameters66 where
  full := (53260557061/500000000000)
  energy := (8652837221/12500000000)
  cov := (74224017641/250000000000)
  schur := (516612339113/500000000000)
  cap := (458917217/500000000000)
  W2 := (3462018708711/1000000000000)
  V := (69317377/250000000000)
  mass := (7768219/1000000000000)
  rootN := (1016476599941/1000000000000)
  rootB := (15147891223/500000000000)
  rootU := (37954438659/62500000000)
  rootV := (2081426449/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_66.scalar_checked
  centre := fun n hn => lowFull3_66 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy66 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_66.bound (by norm_num) hn lowTIParameters66_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_67 : FrameRectangleCertificate 9000 10000 (987/2000) (247/500) lowTIParameters67 where
  full := (53301124941/500000000000)
  energy := (691987561493/1000000000000)
  cov := (59439244077/200000000000)
  schur := (516707695721/500000000000)
  cap := (918624773/1000000000000)
  W2 := (3459132106129/1000000000000)
  V := (34693727/125000000000)
  mass := (3876293/500000000000)
  rootN := (203314081307/200000000000)
  rootB := (30308823353/1000000000000)
  rootU := (75906116473/125000000000)
  rootV := (1665982641/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_67.scalar_checked
  centre := fun n hn => lowFull3_67 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy67 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_67.bound (by norm_num) hn lowTIParameters67_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_68 : FrameRectangleCertificate 9000 10000 (247/500) (989/2000) lowTIParameters68 where
  full := (53341744237/500000000000)
  energy := (691748256849/1000000000000)
  cov := (148748185219/500000000000)
  schur := (206721239909/200000000000)
  cap := (919415259/1000000000000)
  W2 := (3456251648583/1000000000000)
  V := (69457531/250000000000)
  mass := (7738131/1000000000000)
  rootN := (50833212557/50000000000)
  rootB := (1212874443/40000000000)
  rootU := (75903411373/125000000000)
  rootV := (833411849/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_68.scalar_checked
  centre := fun n hn => lowFull3_68 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy68 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_68.bound (by norm_num) hn lowTIParameters68_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_69 : FrameRectangleCertificate 9000 10000 (989/2000) (99/200) lowTIParameters69 where
  full := (106764831347/1000000000000)
  energy := (691509063673/1000000000000)
  cov := (148898260361/500000000000)
  schur := (64612318889/62500000000)
  cap := (920205897/1000000000000)
  W2 := (863344329119/250000000000)
  V := (278110433/1000000000000)
  mass := (1931191/250000000000)
  rootN := (127094766699/125000000000)
  rootB := (15167447849/500000000000)
  rootU := (60720609909/100000000000)
  rootV := (8338321669/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_69.scalar_checked
  centre := fun n hn => lowFull3_69 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy69 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_69.bound (by norm_num) hn lowTIParameters69_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_70 : FrameRectangleCertificate 9000 10000 (99/200) (991/2000) lowTIParameters70 where
  full := (53423139983/500000000000)
  energy := (691269981889/1000000000000)
  cov := (582220061/1953125000)
  schur := (32312128099/31250000000)
  cap := (920996687/1000000000000)
  W2 := (3450509090313/1000000000000)
  V := (139195371/500000000000)
  mass := (7712397/1000000000000)
  rootN := (1016852053727/1000000000000)
  rootB := (7586981807/250000000000)
  rootU := (607185359087/1000000000000)
  rootV := (834252273/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_70.scalar_checked
  centre := fun n hn => lowFull3_70 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy70 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_70.bound (by norm_num) hn lowTIParameters70_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_71 : FrameRectangleCertificate 9000 10000 (991/2000) (62/125) lowTIParameters71 where
  full := (10692783581/100000000000)
  energy := (345515505711/500000000000)
  cov := (74599205493/250000000000)
  schur := (517089595063/500000000000)
  cap := (921787633/1000000000000)
  W2 := (1723823475371/500000000000)
  V := (278671051/1000000000000)
  mass := (3850477/500000000000)
  rootN := (254236502853/250000000000)
  rootB := (30360955733/1000000000000)
  rootU := (151791268499/250000000000)
  rootV := (8346721677/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_71.scalar_checked
  centre := fun n hn => lowFull3_71 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy71 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_71.bound (by norm_num) hn lowTIParameters71_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_72 : FrameRectangleCertificate 9000 10000 (62/125) (993/2000) lowTIParameters72 where
  full := (107009500377/1000000000000)
  energy := (345396076099/500000000000)
  cov := (149348486469/500000000000)
  schur := (51718518739/50000000000)
  cap := (461289369/500000000000)
  W2 := (3444790878411/1000000000000)
  V := (871723/3125000000)
  mass := (7690363/1000000000000)
  rootN := (12713000081/12500000000)
  rootB := (30373981267/1000000000000)
  rootU := (194286479/320000000)
  rootV := (668073481/40000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_72.scalar_checked
  centre := fun n hn => lowFull3_72 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy72 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_72.bound (by norm_num) hn lowTIParameters72_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_73 : FrameRectangleCertificate 9000 10000 (993/2000) (497/1000) lowTIParameters73 where
  full := (5354563759/50000000000)
  energy := (690553404141/1000000000000)
  cov := (74749281033/250000000000)
  schur := (1034561652851/1000000000000)
  cap := (461685003/500000000000)
  W2 := (3441940854091/1000000000000)
  V := (279231669/1000000000000)
  mass := (3840279/500000000000)
  rootN := (1017134038783/1000000000000)
  rootB := (303870039/10000000000)
  rootU := (303562940409/500000000000)
  rootV := (208877831/12500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_73.scalar_checked
  centre := fun n hn => lowFull3_73 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy73 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_73.bound (by norm_num) hn lowTIParameters73_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_74 : FrameRectangleCertificate 9000 10000 (497/1000) (199/400) lowTIParameters74 where
  full := (53586580873/500000000000)
  energy := (690314767177/1000000000000)
  cov := (149648637777/500000000000)
  schur := (1034753024063/1000000000000)
  cap := (462080721/500000000000)
  W2 := (429887107329/125000000000)
  V := (279511979/1000000000000)
  mass := (3835739/500000000000)
  rootN := (63576756761/62500000000)
  rootB := (15200011859/500000000000)
  rootU := (607106978951/1000000000000)
  rootV := (3343722351/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_74.scalar_checked
  centre := fun n hn => lowFull3_74 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy74 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_74.bound (by norm_num) hn lowTIParameters74_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_75 : FrameRectangleCertificate 9000 10000 (199/400) (249/500) lowTIParameters75 where
  full := (5362758081/50000000000)
  energy := (690076241231/1000000000000)
  cov := (299597427201/1000000000000)
  schur := (206988897623/200000000000)
  cap := (184990609/200000000000)
  W2 := (687251774593/200000000000)
  V := (279792289/1000000000000)
  mass := (7663067/1000000000000)
  rootN := (2034644429/2000000000)
  rootB := (30413040707/1000000000000)
  rootU := (607088544439/1000000000000)
  rootV := (8363496413/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_75.scalar_checked
  centre := fun n hn => lowFull3_75 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy75 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_75.bound (by norm_num) hn lowTIParameters75_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_76 : FrameRectangleCertificate 9000 10000 (249/500) (997/2000) lowTIParameters76 where
  full := (26834319091/250000000000)
  energy := (172459456557/250000000000)
  cov := (11995903163/40000000000)
  schur := (103513604473/100000000000)
  cap := (46287241/50000000000)
  W2 := (3433426878083/1000000000000)
  V := (280072599/1000000000000)
  mass := (3827637/500000000000)
  rootN := (1017416357609/1000000000000)
  rootB := (30426054953/1000000000000)
  rootU := (151767645121/250000000000)
  rootV := (16735369701/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_76.scalar_checked
  centre := fun n hn => lowFull3_76 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy76 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_76.bound (by norm_num) hn lowTIParameters76_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_77 : FrameRectangleCertificate 9000 10000 (997/2000) (499/1000) lowTIParameters77 where
  full := (26854876889/250000000000)
  energy := (344799761047/500000000000)
  cov := (150098865587/500000000000)
  schur := (517663846817/500000000000)
  cap := (926536771/1000000000000)
  W2 := (3430600855097/1000000000000)
  V := (280352909/1000000000000)
  mass := (1912013/250000000000)
  rootN := (508755268679/500000000000)
  rootB := (30439066527/1000000000000)
  rootU := (75881636291/125000000000)
  rootV := (1046483899/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_77.scalar_checked
  centre := fun n hn => lowFull3_77 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy77 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_77.bound (by norm_num) hn lowTIParameters77_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_78 : FrameRectangleCertificate 9000 10000 (499/1000) (999/2000) lowTIParameters78 where
  full := (10750185679/100000000000)
  energy := (344680664379/500000000000)
  cov := (37562235437/125000000000)
  schur := (64719964659/62500000000)
  cap := (463664451/500000000000)
  W2 := (3427780785213/1000000000000)
  V := (14031661/50000000000)
  mass := (3820679/500000000000)
  rootN := (508802376799/500000000000)
  rootB := (3806509437/125000000000)
  rootU := (9484938707/15625000000)
  rootV := (261751733/15625000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_78.scalar_checked
  centre := fun n hn => lowFull3_78 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy78 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_78.bound (by norm_num) hn lowTIParameters78_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_79 : FrameRectangleCertificate 9000 10000 (999/2000) (1/2) lowTIParameters79 where
  full := (107584325677/1000000000000)
  energy := (689123246139/1000000000000)
  cov := (60159607209/200000000000)
  schur := (1035711267183/1000000000000)
  cap := (185624243/200000000000)
  W2 := (684993329921/200000000000)
  V := (28091353/100000000000)
  mass := (152703/20000000000)
  rootN := (508849503091/500000000000)
  rootB := (15232540949/500000000000)
  rootU := (607019544549/1000000000000)
  rootV := (523764851/31250000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_79.scalar_checked
  centre := fun n hn => lowFull3_79 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy79 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_79.bound (by norm_num) hn lowTIParameters79_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_80 : FrameRectangleCertificate 9000 10000 (1/2) (1001/2000) lowTIParameters80 where
  full := (53833457923/500000000000)
  energy := (688885274171/1000000000000)
  cov := (11939432611/40000000000)
  schur := (102692317009/100000000000)
  cap := (461751641/500000000000)
  W2 := (855539607419/250000000000)
  V := (278754161/1000000000000)
  mass := (7629393/1000000000000)
  rootN := (25334304437/25000000000)
  rootB := (15194598399/500000000000)
  rootU := (607003495591/1000000000000)
  rootV := (16695932469/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_80.scalar_checked
  centre := fun n hn => lowFull3_80 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy80 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_80.bound (by norm_num) hn lowTIParameters80_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_81 : FrameRectangleCertificate 9000 10000 (1001/2000) (501/1000) lowTIParameters81 where
  full := (53874814471/500000000000)
  energy := (68864741277/100000000000)
  cov := (298783356897/1000000000000)
  schur := (25677837789/25000000000)
  cap := (924291011/1000000000000)
  W2 := (1709678053357/500000000000)
  V := (279032033/1000000000000)
  mass := (7624053/1000000000000)
  rootN := (1013466088017/1000000000000)
  rootB := (3040215471/100000000000)
  rootU := (606987933751/1000000000000)
  rootV := (2088031493/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_81.scalar_checked
  centre := fun n hn => lowFull3_81 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy81 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_81.bound (by norm_num) hn lowTIParameters81_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_82 : FrameRectangleCertificate 9000 10000 (501/1000) (1003/2000) lowTIParameters82 where
  full := (107832466627/1000000000000)
  energy := (688409661873/1000000000000)
  cov := (14954044937/50000000000)
  schur := (1027303943163/1000000000000)
  cap := (185015787/200000000000)
  W2 := (3416559662377/1000000000000)
  V := (139654953/500000000000)
  mass := (7619097/1000000000000)
  rootN := (1013560034317/1000000000000)
  rootB := (7603777577/250000000000)
  rootU := (151743215617/250000000000)
  rootV := (4178141827/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_82.scalar_checked
  centre := fun n hn => lowFull3_82 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy82 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_82.bound (by norm_num) hn lowTIParameters82_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_83 : FrameRectangleCertificate 9000 10000 (1003/2000) (251/500) lowTIParameters83 where
  full := (53957715291/500000000000)
  energy := (3440860107/5000000000)
  cov := (299378440803/1000000000000)
  schur := (513747232293/500000000000)
  cap := (231466763/250000000000)
  W2 := (3413769078089/1000000000000)
  V := (279587779/1000000000000)
  mass := (3807249/500000000000)
  rootN := (506827008107/500000000000)
  rootB := (760701589/25000000000)
  rootU := (303479142599/500000000000)
  rootV := (2090109817/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_83.scalar_checked
  centre := fun n hn => lowFull3_83 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy83 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_83.bound (by norm_num) hn lowTIParameters83_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_84 : FrameRectangleCertificate 9000 10000 (251/500) (201/400) lowTIParameters84 where
  full := (107998522503/1000000000000)
  energy := (687934491279/1000000000000)
  cov := (18729748943/62500000000)
  schur := (1027685075583/1000000000000)
  cap := (231663843/250000000000)
  W2 := (3410984335563/1000000000000)
  V := (69966413/250000000000)
  mass := (1902557/250000000000)
  rootN := (506874016789/500000000000)
  rootB := (6088202927/200000000000)
  rootU := (151736051361/250000000000)
  rootV := (3345837127/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_84.scalar_checked
  centre := fun n hn => lowFull3_84 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy84 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_84.bound (by norm_num) hn lowTIParameters84_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_85 : FrameRectangleCertificate 9000 10000 (201/400) (503/1000) lowTIParameters85 where
  full := (21616348821/200000000000)
  energy := (171924267859/250000000000)
  cov := (37496690699/125000000000)
  schur := (256968943969/250000000000)
  cap := (927443893/1000000000000)
  W2 := (3408205416511/1000000000000)
  V := (11205741/40000000000)
  mass := (7606263/1000000000000)
  rootN := (506921043131/500000000000)
  rootB := (30453963503/1000000000000)
  rootU := (151732656687/250000000000)
  rootV := (16737488611/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_85.scalar_checked
  centre := fun n hn => lowFull3_85 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy85 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_85.bound (by norm_num) hn lowTIParameters85_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_86 : FrameRectangleCertificate 9000 10000 (503/1000) (1007/2000) lowTIParameters86 where
  full := (54082548561/500000000000)
  energy := (3437298809/5000000000)
  cov := (150135534157/500000000000)
  schur := (128508320649/125000000000)
  cap := (928232623/1000000000000)
  W2 := (5320987973/1562500000)
  V := (140210699/500000000000)
  mass := (7602581/1000000000000)
  rootN := (506968087061/500000000000)
  rootB := (30466910297/1000000000000)
  rootU := (606917552693/1000000000000)
  rootV := (16745787471/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_86.scalar_checked
  centre := fun n hn => lowFull3_86 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy86 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_86.bound (by norm_num) hn lowTIParameters86_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_87 : FrameRectangleCertificate 9000 10000 (1007/2000) (63/125) lowTIParameters87 where
  full := (54124291651/500000000000)
  energy := (137444512459/200000000000)
  cov := (37571076407/125000000000)
  schur := (1028257443279/1000000000000)
  cap := (929021563/1000000000000)
  W2 := (425333122007/125000000000)
  V := (35087409/125000000000)
  mass := (7599159/1000000000000)
  rootN := (1014030297023/1000000000000)
  rootB := (7619963759/250000000000)
  rootU := (75863123361/125000000000)
  rootV := (16754082249/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_87.scalar_checked
  centre := fun n hn => lowFull3_87 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy87 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_87.bound (by norm_num) hn lowTIParameters87_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_88 : FrameRectangleCertificate 9000 10000 (63/125) (1009/2000) lowTIParameters88 where
  full := (108332204417/1000000000000)
  energy := (686985472849/1000000000000)
  cov := (300866154417/1000000000000)
  schur := (1028448409861/1000000000000)
  cap := (929810719/1000000000000)
  W2 := (3399903418457/1000000000000)
  V := (140488573/500000000000)
  mass := (379799/50000000000)
  rootN := (1014124454819/1000000000000)
  rootB := (15246398911/500000000000)
  rootU := (606892933001/1000000000000)
  rootV := (16762372923/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_88.scalar_checked
  centre := fun n hn => lowFull3_88 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy88 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_88.bound (by norm_num) hn lowTIParameters88_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_89 : FrameRectangleCertificate 9000 10000 (1009/2000) (101/200) lowTIParameters89 where
  full := (108415962251/1000000000000)
  energy := (686748493389/1000000000000)
  cov := (150581848897/500000000000)
  schur := (514319732339/500000000000)
  cap := (232650023/250000000000)
  W2 := (3397147611993/1000000000000)
  V := (14062751/50000000000)
  mass := (303721/40000000000)
  rootN := (1014218647373/1000000000000)
  rootB := (15252869337/500000000000)
  rootU := (24275255789/40000000000)
  rootV := (16770659499/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_89.scalar_checked
  centre := fun n hn => lowFull3_89 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy89 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_89.bound (by norm_num) hn lowTIParameters89_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_90 : FrameRectangleCertificate 9000 10000 (101/200) (1011/2000) lowTIParameters90 where
  full := (6781241163/62500000000)
  energy := (343255811921/500000000000)
  cov := (18841327587/62500000000)
  schur := (1028830607477/1000000000000)
  cap := (931389687/1000000000000)
  W2 := (1697198769357/500000000000)
  V := (140766447/500000000000)
  mass := (3795139/500000000000)
  rootN := (20286257491/20000000000)
  rootB := (1220747107/40000000000)
  rootU := (606870375789/1000000000000)
  rootV := (16778941981/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_90.scalar_checked
  centre := fun n hn => lowFull3_90 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy90 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_90.bound (by norm_num) hn lowTIParameters90_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_91 : FrameRectangleCertificate 9000 10000 (1011/2000) (253/500) lowTIParameters91 where
  full := (54291947657/500000000000)
  energy := (137254972827/200000000000)
  cov := (60351757041/200000000000)
  schur := (41160873519/40000000000)
  cap := (932179507/1000000000000)
  W2 := (3391653180801/1000000000000)
  V := (17613173/62500000000)
  mass := (1896931/250000000000)
  rootN := (1014407136201/1000000000000)
  rootB := (15265807439/500000000000)
  rootU := (606859879977/1000000000000)
  rootV := (8393610189/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_91.scalar_checked
  centre := fun n hn => lowFull3_91 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy91 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_91.bound (by norm_num) hn lowTIParameters91_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_92 : FrameRectangleCertificate 9000 10000 (253/500) (1013/2000) lowTIParameters92 where
  full := (108668074209/1000000000000)
  energy := (343019107099/500000000000)
  cov := (302056329233/1000000000000)
  schur := (205842631187/200000000000)
  cap := (233242389/250000000000)
  W2 := (847228630141/250000000000)
  V := (282088643/1000000000000)
  mass := (1896337/250000000000)
  rootN := (5072507161/5000000000)
  rootB := (30544550349/1000000000000)
  rootU := (303424955553/500000000000)
  rootV := (4198873681/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_92.scalar_checked
  centre := fun n hn => lowFull3_92 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy92 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_92.bound (by norm_num) hn lowTIParameters92_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_93 : FrameRectangleCertificate 9000 10000 (1013/2000) (507/1000) lowTIParameters93 where
  full := (54376198577/500000000000)
  energy := (685801673953/1000000000000)
  cov := (302353873481/1000000000000)
  schur := (205880912217/200000000000)
  cap := (466879919/500000000000)
  W2 := (423272692527/125000000000)
  V := (141183259/500000000000)
  mass := (3791569/500000000000)
  rootN := (1014595762403/1000000000000)
  rootB := (30557484157/1000000000000)
  rootU := (303420236511/500000000000)
  rootV := (3360752999/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_93.scalar_checked
  centre := fun n hn => lowFull3_93 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy93 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_93.bound (by norm_num) hn lowTIParameters93_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_94 : FrameRectangleCertificate 9000 10000 (507/1000) (203/400) lowTIParameters94 where
  full := (27209216507/250000000000)
  energy := (171391310833/250000000000)
  cov := (151325708971/500000000000)
  schur := (41183842127/40000000000)
  cap := (23363759/25000000000)
  W2 := (1691727111127/500000000000)
  V := (282644393/1000000000000)
  mass := (7581081/1000000000000)
  rootN := (1014690126677/1000000000000)
  rootB := (30570416419/1000000000000)
  rootU := (60683156963/100000000000)
  rootV := (8406015599/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_94.scalar_checked
  centre := fun n hn => lowFull3_94 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy94 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_94.bound (by norm_num) hn lowTIParameters94_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_95 : FrameRectangleCertificate 9000 10000 (203/400) (127/250) lowTIParameters95 where
  full := (10892148273/100000000000)
  energy := (685328922263/1000000000000)
  cov := (15147448131/50000000000)
  schur := (1029787631951/1000000000000)
  cap := (935341121/1000000000000)
  W2 := (3380732549111/1000000000000)
  V := (70730567/250000000000)
  mass := (7579167/1000000000000)
  rootN := (126848065611/125000000000)
  rootB := (30583347119/1000000000000)
  rootU := (303411602433/500000000000)
  rootV := (16820293339/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_95.scalar_checked
  centre := fun n hn => lowFull3_95 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy95 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_95.bound (by norm_num) hn lowTIParameters95_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_96 : FrameRectangleCertificate 9000 10000 (127/250) (1017/2000) lowTIParameters96 where
  full := (109006249177/1000000000000)
  energy := (685092710671/1000000000000)
  cov := (37905813439/125000000000)
  schur := (1029979297147/1000000000000)
  cap := (936132127/1000000000000)
  W2 := (211126031457/62500000000)
  V := (17700009/62500000000)
  mass := (1515477/200000000000)
  rootN := (202975791379/200000000000)
  rootB := (30596276359/1000000000000)
  rootU := (606815382703/1000000000000)
  rootV := (16828551453/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_96.scalar_checked
  centre := fun n hn => lowFull3_96 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy96 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_96.bound (by norm_num) hn lowTIParameters96_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_97 : FrameRectangleCertificate 9000 10000 (1017/2000) (509/1000) lowTIParameters97 where
  full := (54545583653/500000000000)
  energy := (342428304243/500000000000)
  cov := (151772026309/500000000000)
  schur := (16096422633/15625000000)
  cap := (117115423/125000000000)
  W2 := (210956629217/62500000000)
  V := (283478019/1000000000000)
  mass := (3787863/500000000000)
  rootN := (202994684513/200000000000)
  rootB := (30609204237/1000000000000)
  rootU := (606808107161/1000000000000)
  rootV := (16836805487/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_97.scalar_checked
  centre := fun n hn => lowFull3_97 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy97 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_97.bound (by norm_num) hn lowTIParameters97_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_98 : FrameRectangleCertificate 9000 10000 (509/1000) (1019/2000) lowTIParameters98 where
  full := (3411757471/31250000000)
  energy := (171155153909/250000000000)
  cov := (303841597939/1000000000000)
  schur := (515181442903/500000000000)
  cap := (234428723/250000000000)
  W2 := (3372601224317/1000000000000)
  V := (56751179/200000000000)
  mass := (378709/50000000000)
  rootN := (101506792177/100000000000)
  rootB := (7655532689/250000000000)
  rootU := (6068013823/10000000000)
  rootV := (8422527753/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_98.scalar_checked
  centre := fun n hn => lowFull3_98 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy98 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_98.bound (by norm_num) hn lowTIParameters98_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_99 : FrameRectangleCertificate 9000 10000 (1019/2000) (51/100) lowTIParameters99 where
  full := (2185229329/20000000000)
  energy := (42774045753/62500000000)
  cov := (304139143473/1000000000000)
  schur := (1030554808771/1000000000000)
  cap := (469253329/500000000000)
  W2 := (673980391317/200000000000)
  V := (284033771/1000000000000)
  mass := (378637/50000000000)
  rootN := (1624259927/1600000000)
  rootB := (30635056031/1000000000000)
  rootU := (606795212217/1000000000000)
  rootV := (16853301487/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_99.scalar_checked
  centre := fun n hn => lowFull3_99 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy99 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_99.bound (by norm_num) hn lowTIParameters99_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_100 : FrameRectangleCertificate 9000 10000 (51/100) (1021/2000) lowTIParameters100 where
  full := (109346851437/1000000000000)
  energy := (684148957649/1000000000000)
  cov := (301805135841/1000000000000)
  schur := (510922489621/500000000000)
  cap := (466927223/500000000000)
  W2 := (3367208247049/1000000000000)
  V := (56370811/200000000000)
  mass := (7571399/1000000000000)
  rootN := (1010863482001/1000000000000)
  rootB := (30559032151/1000000000000)
  rootU := (121357920211/200000000000)
  rootV := (16788509613/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_100.scalar_checked
  centre := fun n hn => lowFull3_100 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy100 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_100.bound (by norm_num) hn lowTIParameters100_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_101 : FrameRectangleCertificate 9000 10000 (1021/2000) (511/1000) lowTIParameters101 where
  full := (6839524753/62500000000)
  energy := (683913292373/1000000000000)
  cov := (302100102773/1000000000000)
  schur := (204407080927/200000000000)
  cap := (233660463/250000000000)
  W2 := (3364520078719/1000000000000)
  V := (282129523/1000000000000)
  mass := (7570149/1000000000000)
  rootN := (252739416771/250000000000)
  rootB := (7642978199/250000000000)
  rootU := (303392276503/500000000000)
  rootV := (16796711673/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_101.scalar_checked
  centre := fun n hn => lowFull3_101 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy101 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_101.bound (by norm_num) hn lowTIParameters101_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_102 : FrameRectangleCertificate 9000 10000 (511/1000) (1023/2000) lowTIParameters102 where
  full := (109518102317/1000000000000)
  energy := (683677736143/1000000000000)
  cov := (302395069919/1000000000000)
  schur := (1022225914233/1000000000000)
  cap := (467714763/500000000000)
  W2 := (840459358627/250000000000)
  V := (282404991/1000000000000)
  mass := (7568983/1000000000000)
  rootN := (252762971259/250000000000)
  rootB := (15292396199/500000000000)
  rootU := (18961877259/31250000000)
  rootV := (1680490973/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_102.scalar_checked
  centre := fun n hn => lowFull3_102 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy102 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_102.bound (by norm_num) hn lowTIParameters102_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_103 : FrameRectangleCertificate 9000 10000 (1023/2000) (64/125) lowTIParameters103 where
  full := (54801986149/500000000000)
  energy := (683442288889/1000000000000)
  cov := (12107601491/40000000000)
  schur := (12780206347/12500000000)
  cap := (936217477/1000000000000)
  W2 := (419895037179/125000000000)
  V := (282680459/1000000000000)
  mass := (7567897/1000000000000)
  rootN := (101114613571/100000000000)
  rootB := (6119534221/200000000000)
  rootU := (121355232633/200000000000)
  rootV := (16813103789/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_103.scalar_checked
  centre := fun n hn => lowFull3_103 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy103 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_103.bound (by norm_num) hn lowTIParameters103_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_104 : FrameRectangleCertificate 9000 10000 (64/125) (41/80) lowTIParameters104 where
  full := (109690008067/1000000000000)
  energy := (683206950541/1000000000000)
  cov := (151492502419/500000000000)
  schur := (1022607184983/1000000000000)
  cap := (187401141/200000000000)
  W2 := (3356488650639/1000000000000)
  V := (35369491/125000000000)
  mass := (7566883/1000000000000)
  rootN := (1011240418983/1000000000000)
  rootB := (30610548917/1000000000000)
  rootU := (12135456599/20000000000)
  rootV := (16821293887/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_104.scalar_checked
  centre := fun n hn => lowFull3_104 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy104 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_104.bound (by norm_num) hn lowTIParameters104_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_105 : FrameRectangleCertificate 9000 10000 (41/80) (513/1000) lowTIParameters105 where
  full := (54888105861/500000000000)
  energy := (341485860513/500000000000)
  cov := (1184687393/3906250000)
  schur := (20455958913/20000000000)
  cap := (117224277/125000000000)
  W2 := (1676911238641/500000000000)
  V := (70807849/250000000000)
  mass := (3782969/500000000000)
  rootN := (1580210523/1562500000)
  rootB := (1913964121/62500000000)
  rootU := (303385038501/500000000000)
  rootV := (16829479969/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_105.scalar_checked
  centre := fun n hn => lowFull3_105 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy105 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_105.bound (by norm_num) hn lowTIParameters105_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_106 : FrameRectangleCertificate 9000 10000 (513/1000) (1027/2000) lowTIParameters106 where
  full := (878900683/8000000000)
  energy := (27309464011/40000000000)
  cov := (30357494059/100000000000)
  schur := (63936799347/62500000000)
  cap := (469291507/500000000000)
  W2 := (1675580880331/500000000000)
  V := (56701373/200000000000)
  mass := (29551/3906250000)
  rootN := (101142908281/100000000000)
  rootB := (1225452089/40000000000)
  rootU := (606767908707/1000000000000)
  rootV := (16837662101/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_106.scalar_checked
  centre := fun n hn => lowFull3_106 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy106 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_106.bound (by norm_num) hn lowTIParameters106_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_107 : FrameRectangleCertificate 9000 10000 (1027/2000) (257/500) lowTIParameters107 where
  full := (21989826233/200000000000)
  energy := (136500317643/200000000000)
  cov := (303869908777/1000000000000)
  schur := (1023179716419/1000000000000)
  cap := (117421513/125000000000)
  W2 := (669701296807/200000000000)
  V := (141891167/500000000000)
  mass := (7564233/1000000000000)
  rootN := (1011523463109/1000000000000)
  rootB := (30649177869/1000000000000)
  rootU := (121353265901/200000000000)
  rootV := (16845840259/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_107.scalar_checked
  centre := fun n hn => lowFull3_107 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy107 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_107.bound (by norm_num) hn lowTIParameters107_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_108 : FrameRectangleCertificate 9000 10000 (257/500) (1029/2000) lowTIParameters108 where
  full := (6877240703/62500000000)
  energy := (85283335597/125000000000)
  cov := (12166595087/40000000000)
  schur := (63960670377/62500000000)
  cap := (940161491/1000000000000)
  W2 := (1672928315417/500000000000)
  V := (71014451/250000000000)
  mass := (1512693/200000000000)
  rootN := (1011617875501/1000000000000)
  rootB := (30662052949/1000000000000)
  rootU := (4854122751/8000000000)
  rootV := (8427007239/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_108.scalar_checked
  centre := fun n hn => lowFull3_108 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy108 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_108.bound (by norm_num) hn lowTIParameters108_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_109 : FrameRectangleCertificate 9000 10000 (1029/2000) (103/200) lowTIParameters109 where
  full := (22024549561/200000000000)
  energy := (682031889889/1000000000000)
  cov := (304459845777/1000000000000)
  schur := (1023561818143/1000000000000)
  cap := (470475589/500000000000)
  W2 := (3343212184507/1000000000000)
  V := (284333273/1000000000000)
  mass := (1890687/250000000000)
  rootN := (505856159927/500000000000)
  rootB := (6134985503/200000000000)
  rootU := (606764956349/1000000000000)
  rootV := (3372436941/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_109.scalar_checked
  centre := fun n hn => lowFull3_109 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy109 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_109.bound (by norm_num) hn lowTIParameters109_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_110 : FrameRectangleCertificate 9000 10000 (103/200) (1031/2000) lowTIParameters110 where
  full := (55104911517/500000000000)
  energy := (681797203479/1000000000000)
  cov := (304754814587/1000000000000)
  schur := (1023752992509/1000000000000)
  cap := (941741171/1000000000000)
  W2 := (334057312853/100000000000)
  V := (284608743/1000000000000)
  mass := (7562079/1000000000000)
  rootN := (1011806796039/1000000000000)
  rootB := (6137560333/200000000000)
  rootU := (303382585743/500000000000)
  rootV := (3374070201/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_110.scalar_checked
  centre := fun n hn => lowFull3_110 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy110 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_110.bound (by norm_num) hn lowTIParameters110_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_111 : FrameRectangleCertificate 9000 10000 (1031/2000) (129/250) lowTIParameters111 where
  full := (27574269789/250000000000)
  energy := (340781312741/500000000000)
  cov := (152524891801/500000000000)
  schur := (204788849783/200000000000)
  cap := (471265737/500000000000)
  W2 := (3337939446593/1000000000000)
  V := (284884213/1000000000000)
  mass := (7561453/1000000000000)
  rootN := (50595065197/50000000000)
  rootB := (6140135093/200000000000)
  rootU := (121353198781/200000000000)
  rootV := (16878513353/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_111.scalar_checked
  centre := fun n hn => lowFull3_111 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy111 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_111.bound (by norm_num) hn lowTIParameters111_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_112 : FrameRectangleCertificate 9000 10000 (129/250) (1033/2000) lowTIParameters112 where
  full := (110384518413/1000000000000)
  energy := (340664077911/500000000000)
  cov := (38168094103/125000000000)
  schur := (102413558711/100000000000)
  cap := (943322091/1000000000000)
  W2 := (3335311122251/1000000000000)
  V := (285159683/1000000000000)
  mass := (7560869/1000000000000)
  rootN := (505997921713/500000000000)
  rootB := (30713548981/1000000000000)
  rootU := (151691857063/250000000000)
  rootV := (16886671757/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_112.scalar_checked
  centre := fun n hn => lowFull3_112 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy112 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_112.bound (by norm_num) hn lowTIParameters112_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_113 : FrameRectangleCertificate 9000 10000 (1033/2000) (517/1000) lowTIParameters113 where
  full := (110472143069/1000000000000)
  energy := (681093794431/1000000000000)
  cov := (305639722249/1000000000000)
  schur := (51216350343/50000000000)
  cap := (944113027/1000000000000)
  W2 := (3332688139289/1000000000000)
  V := (285435153/1000000000000)
  mass := (7560323/1000000000000)
  rootN := (1012090414371/1000000000000)
  rootB := (6145284459/200000000000)
  rootU := (606769479233/1000000000000)
  rootV := (844741311/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_113.scalar_checked
  centre := fun n hn => lowFull3_113 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy113 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_113.bound (by norm_num) hn lowTIParameters113_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_114 : FrameRectangleCertificate 9000 10000 (517/1000) (207/400) lowTIParameters114 where
  full := (11055995541/100000000000)
  energy := (340429770619/500000000000)
  cov := (7648367297/25000000000)
  schur := (204903701589/200000000000)
  cap := (472452143/500000000000)
  W2 := (666014096297/200000000000)
  V := (285710623/1000000000000)
  mass := (7559813/1000000000000)
  rootN := (506092508329/500000000000)
  rootB := (30739295471/1000000000000)
  rootU := (60677215159/100000000000)
  rootV := (67611907/4000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_114.scalar_checked
  centre := fun n hn => lowFull3_114 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy114 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_114.bound (by norm_num) hn lowTIParameters114_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_115 : FrameRectangleCertificate 9000 10000 (207/400) (259/500) lowTIParameters115 where
  full := (110647957741/1000000000000)
  energy := (680625396173/1000000000000)
  cov := (61245932343/200000000000)
  schur := (256177522529/250000000000)
  cap := (7565567/8000000000)
  W2 := (3327458132661/1000000000000)
  V := (142993047/500000000000)
  mass := (7559337/1000000000000)
  rootN := (202455930031/200000000000)
  rootB := (30752168623/1000000000000)
  rootU := (606775450103/1000000000000)
  rootV := (16911123381/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_115.scalar_checked
  centre := fun n hn => lowFull3_115 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy115 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_115.bound (by norm_num) hn lowTIParameters115_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_116 : FrameRectangleCertificate 9000 10000 (259/500) (1037/2000) lowTIParameters116 where
  full := (55368076197/500000000000)
  energy := (680391359169/1000000000000)
  cov := (38315578969/125000000000)
  schur := (64056359573/62500000000)
  cap := (189297559/200000000000)
  W2 := (3324851076821/1000000000000)
  V := (57252313/200000000000)
  mass := (7558891/1000000000000)
  rootN := (3954587167/3906250000)
  rootB := (30765041769/1000000000000)
  rootU := (606779379619/1000000000000)
  rootV := (1691926609/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_116.scalar_checked
  centre := fun n hn => lowFull3_116 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy116 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_116.bound (by norm_num) hn lowTIParameters116_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_117 : FrameRectangleCertificate 9000 10000 (1037/2000) (519/1000) lowTIParameters117 where
  full := (55412270859/500000000000)
  energy := (13603148603/20000000000)
  cov := (153409800997/500000000000)
  schur := (205018699369/200000000000)
  cap := (473640027/500000000000)
  W2 := (3322249297841/1000000000000)
  V := (71634259/250000000000)
  mass := (3779237/500000000000)
  rootN := (506234505157/500000000000)
  rootB := (30777915037/1000000000000)
  rootU := (303391972499/500000000000)
  rootV := (16927404881/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_117.scalar_checked
  centre := fun n hn => lowFull3_117 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy117 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_117.bound (by norm_num) hn lowTIParameters117_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_118 : FrameRectangleCertificate 9000 10000 (519/1000) (1039/2000) lowTIParameters118 where
  full := (110913128087/1000000000000)
  energy := (169980902263/250000000000)
  cov := (153557286219/500000000000)
  schur := (51264266047/50000000000)
  cap := (948072657/1000000000000)
  W2 := (3319652779871/1000000000000)
  V := (286812507/1000000000000)
  mass := (1511617/200000000000)
  rootN := (101256373673/100000000000)
  rootB := (30790788509/1000000000000)
  rootU := (606789151171/1000000000000)
  rootV := (8467769881/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_118.scalar_checked
  centre := fun n hn => lowFull3_118 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy118 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_118.bound (by norm_num) hn lowTIParameters118_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_119 : FrameRectangleCertificate 9000 10000 (1039/2000) (13/25) lowTIParameters119 where
  full := (1110019139/10000000000)
  energy := (135937979161/200000000000)
  cov := (307409543083/1000000000000)
  schur := (51273861261/50000000000)
  cap := (118608201/125000000000)
  W2 := (51829086047/15625000000)
  V := (143543989/500000000000)
  mass := (188943/25000000000)
  rootN := (1012658493877/1000000000000)
  rootB := (123214649/4000000000)
  rootU := (606795003113/1000000000000)
  rootV := (1058979421/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_119.scalar_checked
  centre := fun n hn => lowFull3_119 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy119 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_119.bound (by norm_num) hn lowTIParameters119_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_120 : FrameRectangleCertificate 9000 10000 (13/25) (1041/2000) lowTIParameters120 where
  full := (11109090157/100000000000)
  energy := (135891258067/200000000000)
  cov := (30505404037/100000000000)
  schur := (1016842650893/1000000000000)
  cap := (472090701/500000000000)
  W2 := (16572377317/5000000000)
  V := (71222047/250000000000)
  mass := (7557379/1000000000000)
  rootN := (504193080797/500000000000)
  rootB := (7681883729/250000000000)
  rootU := (606801505817/1000000000000)
  rootV := (8439315553/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_120.scalar_checked
  centre := fun n hn => lowFull3_120 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy120 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_120.bound (by norm_num) hn lowTIParameters120_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_121 : FrameRectangleCertificate 9000 10000 (1041/2000) (521/1000) lowTIParameters121 where
  full := (13897511693/125000000000)
  energy := (5306428067/7812500000)
  cov := (305346463753/1000000000000)
  schur := (63564565807/62500000000)
  cap := (472485123/500000000000)
  W2 := (3311894633311/1000000000000)
  V := (891129/3125000000)
  mass := (377853/50000000000)
  rootN := (1008480566453/1000000000000)
  rootB := (15370184173/500000000000)
  rootU := (303404332179/500000000000)
  rootV := (8443359521/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_121.scalar_checked
  centre := fun n hn => lowFull3_121 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy121 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_121.bound (by norm_num) hn lowTIParameters121_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_122 : FrameRectangleCertificate 9000 10000 (521/1000) (1043/2000) lowTIParameters122 where
  full := (55634746141/500000000000)
  energy := (339494701229/500000000000)
  cov := (152819443667/500000000000)
  schur := (1017223533749/1000000000000)
  cap := (236439863/250000000000)
  W2 := (413664875131/125000000000)
  V := (285434373/1000000000000)
  mass := (7556761/1000000000000)
  rootN := (1008575001549/1000000000000)
  rootB := (6150640461/200000000000)
  rootU := (606816483829/1000000000000)
  rootV := (263981299/15625000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_122.scalar_checked
  centre := fun n hn => lowFull3_122 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy122 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_122.bound (by norm_num) hn lowTIParameters122_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_123 : FrameRectangleCertificate 9000 10000 (1043/2000) (261/500) lowTIParameters123 where
  full := (6959943767/62500000000)
  energy := (84844514989/125000000000)
  cov := (61186262223/200000000000)
  schur := (508707046599/500000000000)
  cap := (946549027/1000000000000)
  W2 := (3306748550983/1000000000000)
  V := (142853733/500000000000)
  mass := (7556481/1000000000000)
  rootN := (252167366693/250000000000)
  rootB := (7691509227/250000000000)
  rootU := (606824969381/1000000000000)
  rootV := (4225720841/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_123.scalar_checked
  centre := fun n hn => lowFull3_123 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy123 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_123.bound (by norm_num) hn lowTIParameters123_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_124 : FrameRectangleCertificate 9000 10000 (261/500) (209/400) lowTIParameters124 where
  full := (55724460013/500000000000)
  energy := (678522944871/1000000000000)
  cov := (153111867547/500000000000)
  schur := (1017604731037/1000000000000)
  cap := (473669487/500000000000)
  W2 := (3304183267603/1000000000000)
  V := (285980559/1000000000000)
  mass := (7556219/1000000000000)
  rootN := (252190990501/250000000000)
  rootB := (15389436101/500000000000)
  rootU := (303417063109/500000000000)
  rootV := (16910959731/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_124.scalar_checked
  centre := fun n hn => lowFull3_124 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy124 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_124.bound (by norm_num) hn lowTIParameters124_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_125 : FrameRectangleCertificate 9000 10000 (209/400) (523/1000) lowTIParameters125 where
  full := (111538954077/1000000000000)
  energy := (33914493863/50000000000)
  cov := (76629039817/250000000000)
  schur := (127224430877/125000000000)
  cap := (474064651/500000000000)
  W2 := (206351445957/62500000000)
  V := (71563413/250000000000)
  mass := (3777987/500000000000)
  rootN := (126107310889/125000000000)
  rootB := (7697927083/250000000000)
  rootU := (606843959573/1000000000000)
  rootV := (8459516121/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_125.scalar_checked
  centre := fun n hn => lowFull3_125 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy125 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_125.bound (by norm_num) hn lowTIParameters125_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_126 : FrameRectangleCertificate 9000 10000 (523/1000) (1047/2000) lowTIParameters126 where
  full := (111629204981/1000000000000)
  energy := (84757114627/125000000000)
  cov := (153404291821/500000000000)
  schur := (1017986240963/1000000000000)
  cap := (948920013/1000000000000)
  W2 := (3299068138741/1000000000000)
  V := (143263373/500000000000)
  mass := (236117/31250000000)
  rootN := (1008953042001/1000000000000)
  rootB := (30804545331/1000000000000)
  rootU := (121370894947/200000000000)
  rootV := (8463550467/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_126.scalar_checked
  centre := fun n hn => lowFull3_126 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy126 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_126.bound (by norm_num) hn lowTIParameters126_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_127 : FrameRectangleCertificate 9000 10000 (1047/2000) (131/250) lowTIParameters127 where
  full := (111719675319/1000000000000)
  energy := (169456016017/250000000000)
  cov := (30710100821/100000000000)
  schur := (1018177112627/1000000000000)
  cap := (189942223/200000000000)
  W2 := (3296518262489/1000000000000)
  V := (286799839/1000000000000)
  mass := (7555529/1000000000000)
  rootN := (1009047626541/1000000000000)
  rootB := (15408691663/500000000000)
  rootU := (7585820963/12500000000)
  rootV := (16935165751/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_127.scalar_checked
  centre := fun n hn => lowFull3_127 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy127 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_127.bound (by norm_num) hn lowTIParameters127_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_128 : FrameRectangleCertificate 9000 10000 (131/250) (1049/2000) lowTIParameters128 where
  full := (6988147981/62500000000)
  energy := (338795659173/500000000000)
  cov := (307393432977/1000000000000)
  schur := (101836806181/100000000000)
  cap := (950502611/1000000000000)
  W2 := (823493372809/250000000000)
  V := (287072933/1000000000000)
  mass := (7555327/1000000000000)
  rootN := (63071390039/62500000000)
  rootB := (7707555591/250000000000)
  rootU := (151719392967/250000000000)
  rootV := (16943226759/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_128.scalar_checked
  centre := fun n hn => lowFull3_128 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy128 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_128.bound (by norm_num) hn lowTIParameters128_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_129 : FrameRectangleCertificate 9000 10000 (1049/2000) (21/40) lowTIParameters129 where
  full := (111901284739/1000000000000)
  energy := (338679339891/500000000000)
  cov := (307685857939/1000000000000)
  schur := (1018559088291/1000000000000)
  cap := (475647253/500000000000)
  W2 := (3291433809721/1000000000000)
  V := (287346027/1000000000000)
  mass := (3777569/500000000000)
  rootN := (252309221033/250000000000)
  rootB := (30843062527/1000000000000)
  rootU := (151722541161/250000000000)
  rootV := (8475641967/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_129.scalar_checked
  centre := fun n hn => lowFull3_129 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy129 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_129.bound (by norm_num) hn lowTIParameters129_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_130 : FrameRectangleCertificate 9000 10000 (21/40) (1051/2000) lowTIParameters130 where
  full := (111992429103/1000000000000)
  energy := (677126148311/1000000000000)
  cov := (61595656619/200000000000)
  schur := (254687547967/250000000000)
  cap := (952086809/1000000000000)
  W2 := (1644449601409/500000000000)
  V := (287619121/1000000000000)
  mass := (7554961/1000000000000)
  rootN := (1009331556957/1000000000000)
  rootB := (30855903957/1000000000000)
  rootU := (75862932607/125000000000)
  rootV := (16959337281/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_130.scalar_checked
  centre := fun n hn => lowFull3_130 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy130 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_130.bound (by norm_num) hn lowTIParameters130_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_131 : FrameRectangleCertificate 9000 10000 (1051/2000) (263/500) lowTIParameters131 where
  full := (112083803463/1000000000000)
  energy := (676893723859/1000000000000)
  cov := (154135354223/500000000000)
  schur := (1018941372301/1000000000000)
  cap := (5955497/6250000000)
  W2 := (6418690733/1953125000)
  V := (57578443/200000000000)
  mass := (1510959/200000000000)
  rootN := (252356564743/250000000000)
  rootB := (6173749331/200000000000)
  rootU := (606917466013/1000000000000)
  rootV := (8483693403/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_131.scalar_checked
  centre := fun n hn => lowFull3_131 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy131 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_131.bound (by norm_num) hn lowTIParameters131_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_132 : FrameRectangleCertificate 9000 10000 (263/500) (1053/2000) lowTIParameters132 where
  full := (112175410521/1000000000000)
  energy := (676661406363/1000000000000)
  cov := (308563133993/1000000000000)
  schur := (509566314709/500000000000)
  cap := (953672649/1000000000000)
  W2 := (410480644023/125000000000)
  V := (28816531/100000000000)
  mass := (7554639/1000000000000)
  rootN := (1009520990083/1000000000000)
  rootB := (30881590779/1000000000000)
  rootU := (18966630803/31250000000)
  rootV := (16975432543/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_132.scalar_checked
  centre := fun n hn => lowFull3_132 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy132 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_132.bound (by norm_num) hn lowTIParameters132_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_133 : FrameRectangleCertificate 9000 10000 (1053/2000) (527/1000) lowTIParameters133 where
  full := (112267253/1000000000)
  energy := (84553649469/125000000000)
  cov := (77213889933/250000000000)
  schur := (40772958519/40000000000)
  cap := (954466201/1000000000000)
  W2 := (328132567839/100000000000)
  V := (57687681/200000000000)
  mass := (7554493/1000000000000)
  rootN := (504807875081/500000000000)
  rootB := (30894436409/1000000000000)
  rootU := (60694762551/100000000000)
  rootV := (4245868617/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_133.scalar_checked
  centre := fun n hn => lowFull3_133 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy133 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_133.bound (by norm_num) hn lowTIParameters133_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_134 : FrameRectangleCertificate 9000 10000 (527/1000) (211/400) lowTIParameters134 where
  full := (56179666827/500000000000)
  energy := (16904927299/25000000000)
  cov := (61829597133/200000000000)
  schur := (203903074557/200000000000)
  cap := (477630091/500000000000)
  W2 := (3278811219043/1000000000000)
  V := (577423/2000000000)
  mass := (1888589/250000000000)
  rootN := (252427634777/250000000000)
  rootB := (772682091/25000000000)
  rootU := (121392758227/200000000000)
  rootV := (4247878147/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_134.scalar_checked
  centre := fun n hn => lowFull3_134 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy134 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_134.bound (by norm_num) hn lowTIParameters134_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_135 : FrameRectangleCertificate 9000 10000 (211/400) (66/125) lowTIParameters135 where
  full := (14056456907/125000000000)
  energy := (135193018983/200000000000)
  cov := (309440411791/1000000000000)
  schur := (1019706858621/1000000000000)
  cap := (239013649/250000000000)
  W2 := (51192214987/15625000000)
  V := (57796919/200000000000)
  mass := (7554227/1000000000000)
  rootN := (157782087/156250000)
  rootB := (3865016567/125000000000)
  rootU := (303490344137/500000000000)
  rootV := (8499773453/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_135.scalar_checked
  centre := fun n hn => lowFull3_135 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy135 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_135.bound (by norm_num) hn lowTIParameters135_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_136 : FrameRectangleCertificate 9000 10000 (66/125) (1057/2000) lowTIParameters136 where
  full := (112544220607/1000000000000)
  energy := (84466650569/125000000000)
  cov := (309732838111/1000000000000)
  schur := (1019898420289/1000000000000)
  cap := (478424723/500000000000)
  W2 := (1636898641989/500000000000)
  V := (28925769/100000000000)
  mass := (7554107/1000000000000)
  rootN := (504950101567/500000000000)
  rootB := (30932983141/1000000000000)
  rootU := (151749580673/250000000000)
  rootV := (17007577429/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_136.scalar_checked
  centre := fun n hn => lowFull3_136 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy136 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_136.bound (by norm_num) hn lowTIParameters136_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_137 : FrameRectangleCertificate 9000 10000 (1057/2000) (529/1000) lowTIParameters137 where
  full := (112637032531/1000000000000)
  energy := (675501420803/1000000000000)
  cov := (155012632311/500000000000)
  schur := (255022514393/250000000000)
  cap := (119705593/125000000000)
  W2 := (654259555737/200000000000)
  V := (57906157/200000000000)
  mass := (7553993/1000000000000)
  rootN := (504997538997/500000000000)
  rootB := (30945835649/1000000000000)
  rootU := (151754175049/250000000000)
  rootV := (17015604163/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_137.scalar_checked
  centre := fun n hn => lowFull3_137 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy137 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_137.bound (by norm_num) hn lowTIParameters137_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_138 : FrameRectangleCertificate 9000 10000 (529/1000) (1059/2000) lowTIParameters138 where
  full := (56365046941/500000000000)
  energy := (675269743601/1000000000000)
  cov := (155158845661/500000000000)
  schur := (204056354053/200000000000)
  cap := (239610123/250000000000)
  W2 := (3268803228617/1000000000000)
  V := (289803881/1000000000000)
  mass := (7553887/1000000000000)
  rootN := (126261247659/125000000000)
  rootB := (30958690089/1000000000000)
  rootU := (18969869583/31250000000)
  rootV := (851181357/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_138.scalar_checked
  centre := fun n hn => lowFull3_138 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy138 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_138.bound (by norm_num) hn lowTIParameters138_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_139 : FrameRectangleCertificate 9000 10000 (1059/2000) (53/100) lowTIParameters139 where
  full := (11282340753/100000000000)
  energy := (168759543219/250000000000)
  cov := (62122023643/200000000000)
  schur := (12755919477/12500000000)
  cap := (479618349/500000000000)
  W2 := (816578404763/250000000000)
  V := (290076977/1000000000000)
  mass := (7553787/1000000000000)
  rootN := (126273114107/125000000000)
  rootB := (7742886647/250000000000)
  rootU := (607055707957/1000000000000)
  rootV := (17031646339/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_139.scalar_checked
  centre := fun n hn => lowFull3_139 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy139 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_139.bound (by norm_num) hn lowTIParameters139_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_140 : FrameRectangleCertificate 9000 10000 (53/100) (1061/2000) lowTIParameters140 where
  full := (56458488191/500000000000)
  energy := (134961341713/200000000000)
  cov := (30823340551/100000000000)
  schur := (1011911402887/1000000000000)
  cap := (954523133/1000000000000)
  W2 := (1631914467733/500000000000)
  V := (143928689/500000000000)
  mass := (7553693/1000000000000)
  rootN := (10059380711/10000000000)
  rootB := (30895357791/1000000000000)
  rootU := (151769087519/250000000000)
  rootV := (4241590047/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_140.scalar_checked
  centre := fun n hn => lowFull3_140 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy140 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_140.bound (by norm_num) hn lowTIParameters140_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_141 : FrameRectangleCertificate 9000 10000 (1061/2000) (531/1000) lowTIParameters141 where
  full := (22602160673/200000000000)
  energy := (168643837649/250000000000)
  cov := (154261657767/500000000000)
  schur := (1012101685337/1000000000000)
  cap := (2985361/3125000000)
  W2 := (326134916327/100000000000)
  V := (72032031/250000000000)
  mass := (1510721/200000000000)
  rootN := (1006032646259/1000000000000)
  rootB := (30908178853/1000000000000)
  rootU := (60709775901/100000000000)
  rootV := (16974337219/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_141.scalar_checked
  centre := fun n hn => lowFull3_141 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy141 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_141.bound (by norm_num) hn lowTIParameters141_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_142 : FrameRectangleCertificate 9000 10000 (531/1000) (1063/2000) lowTIParameters142 where
  full := (113104891429/1000000000000)
  energy := (134868819781/200000000000)
  cov := (19300826609/62500000000)
  schur := (202458408349/200000000000)
  cap := (47805419/50000000000)
  W2 := (1629437144009/500000000000)
  V := (288398869/1000000000000)
  mass := (7553523/1000000000000)
  rootN := (1006127249281/1000000000000)
  rootB := (3865125281/125000000000)
  rootU := (607119940809/1000000000000)
  rootV := (16982310473/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_142.scalar_checked
  centre := fun n hn => lowFull3_142 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy142 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_142.bound (by norm_num) hn lowTIParameters142_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_143 : FrameRectangleCertificate 9000 10000 (1063/2000) (133/250) lowTIParameters143 where
  full := (28299810889/250000000000)
  energy := (674112953423/1000000000000)
  cov := (309103136141/1000000000000)
  schur := (1012482471901/1000000000000)
  cap := (478450861/500000000000)
  W2 := (814101073813/250000000000)
  V := (57733923/200000000000)
  mass := (1510689/200000000000)
  rootN := (201244376011/200000000000)
  rootB := (15466914059/500000000000)
  rootU := (607142901577/1000000000000)
  rootV := (1061892501/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_143.scalar_checked
  centre := fun n hn => lowFull3_143 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy143 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_143.bound (by norm_num) hn lowTIParameters143_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_144 : FrameRectangleCertificate 9000 10000 (133/250) (213/400) lowTIParameters144 where
  full := (113293862753/1000000000000)
  energy := (336940957041/500000000000)
  cov := (12375721869/40000000000)
  schur := (3955753811/3906250000)
  cap := (957695553/1000000000000)
  W2 := (1626969585303/500000000000)
  V := (288940361/1000000000000)
  mass := (1888343/250000000000)
  rootN := (1006316538479/1000000000000)
  rootB := (30946656573/1000000000000)
  rootU := (37947915467/62500000000)
  rootV := (8499122911/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_144.scalar_checked
  centre := fun n hn => lowFull3_144 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy144 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_144.bound (by norm_num) hn lowTIParameters144_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_145 : FrameRectangleCertificate 9000 10000 (213/400) (533/1000) lowTIParameters145 where
  full := (113388752049/1000000000000)
  energy := (673650980819/1000000000000)
  cov := (38710369687/125000000000)
  schur := (10128635527/10000000000)
  cap := (958489877/1000000000000)
  W2 := (3251478899803/1000000000000)
  V := (289211107/1000000000000)
  mass := (7553303/1000000000000)
  rootN := (1006411224451/1000000000000)
  rootB := (15479743837/500000000000)
  rootU := (37949449043/62500000000)
  rootV := (2125775987/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_145.scalar_checked
  centre := fun n hn => lowFull3_145 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy145 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_145.bound (by norm_num) hn lowTIParameters145_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_146 : FrameRectangleCertificate 9000 10000 (533/1000) (1067/2000) lowTIParameters146 where
  full := (14185489313/125000000000)
  energy := (336710076781/500000000000)
  cov := (154986434227/500000000000)
  schur := (15828971921/15625000000)
  cap := (959284701/1000000000000)
  W2 := (406127933567/125000000000)
  V := (289481853/1000000000000)
  mass := (7553239/1000000000000)
  rootN := (1006505937859/1000000000000)
  rootB := (30972321531/1000000000000)
  rootU := (607216519477/1000000000000)
  rootV := (3402833249/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_146.scalar_checked
  centre := fun n hn => lowFull3_146 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy146 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_146.bound (by norm_num) hn lowTIParameters146_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_147 : FrameRectangleCertificate 9000 10000 (1067/2000) (267/500) lowTIParameters147 where
  full := (113579353203/1000000000000)
  energy := (2692757729/4000000000)
  cov := (77565694899/250000000000)
  schur := (1013244926167/1000000000000)
  cap := (96008003/100000000000)
  W2 := (811643215673/250000000000)
  V := (289752599/1000000000000)
  mass := (3776589/500000000000)
  rootN := (201320135721/200000000000)
  rootB := (15492579111/500000000000)
  rootU := (121448531629/200000000000)
  rootV := (17022120873/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_147.scalar_checked
  centre := fun n hn => lowFull3_147 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy147 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_147.bound (by norm_num) hn lowTIParameters147_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_148 : FrameRectangleCertificate 9000 10000 (267/500) (1069/2000) lowTIParameters148 where
  full := (5683753563/50000000000)
  energy := (168239704203/250000000000)
  cov := (310552690923/1000000000000)
  schur := (1013435722157/1000000000000)
  cap := (960875873/1000000000000)
  W2 := (3244127068057/1000000000000)
  V := (145011673/500000000000)
  mass := (7553121/1000000000000)
  rootN := (1006695446577/1000000000000)
  rootB := (30997997887/1000000000000)
  rootU := (607269607043/1000000000000)
  rootV := (3406014363/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_148.scalar_checked
  centre := fun n hn => lowFull3_148 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy148 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_148.bound (by norm_num) hn lowTIParameters148_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_149 : FrameRectangleCertificate 9000 10000 (1069/2000) (107/200) lowTIParameters149 where
  full := (113771071811/1000000000000)
  energy := (336364153591/500000000000)
  cov := (155421301217/500000000000)
  schur := (506813295361/500000000000)
  cap := (192334447/200000000000)
  W2 := (3241686070559/1000000000000)
  V := (72573523/250000000000)
  mass := (7553067/1000000000000)
  rootN := (1006790241671/1000000000000)
  rootB := (6202168121/200000000000)
  rootU := (151824343141/250000000000)
  rootV := (17038019017/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_149.scalar_checked
  centre := fun n hn => lowFull3_149 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy149 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_149.bound (by norm_num) hn lowTIParameters149_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_150 : FrameRectangleCertificate 9000 10000 (107/200) (1071/2000) lowTIParameters150 where
  full := (4554694321/40000000000)
  energy := (10507779739/15625000000)
  cov := (77783128533/250000000000)
  schur := (253454382923/250000000000)
  cap := (962469121/1000000000000)
  W2 := (161962492809/50000000000)
  V := (290564839/1000000000000)
  mass := (7553017/1000000000000)
  rootN := (201377012759/200000000000)
  rootB := (31023686451/1000000000000)
  rootU := (303662980583/500000000000)
  rootV := (17045962543/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_150.scalar_checked
  centre := fun n hn => lowFull3_150 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy150 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_150.bound (by norm_num) hn lowTIParameters150_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_151 : FrameRectangleCertificate 9000 10000 (1071/2000) (67/125) lowTIParameters151 where
  full := (113963933097/1000000000000)
  energy := (134453521017/200000000000)
  cov := (31142242601/100000000000)
  schur := (1014008544843/1000000000000)
  cap := (48163327/50000000000)
  W2 := (1618409205479/500000000000)
  V := (145417793/500000000000)
  mass := (7552969/1000000000000)
  rootN := (100697991283/100000000000)
  rootB := (31036535567/1000000000000)
  rootU := (607355379357/1000000000000)
  rootV := (17053902369/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_151.scalar_checked
  centre := fun n hn => lowFull3_151 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy151 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_151.bound (by norm_num) hn lowTIParameters151_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_152 : FrameRectangleCertificate 9000 10000 (67/125) (1073/2000) lowTIParameters152 where
  full := (57030400123/500000000000)
  energy := (336018706243/500000000000)
  cov := (38964042259/125000000000)
  schur := (507099815003/500000000000)
  cap := (482032249/500000000000)
  W2 := (646878344193/200000000000)
  V := (291106333/1000000000000)
  mass := (1888231/250000000000)
  rootN := (503537394343/500000000000)
  rootB := (15524694023/500000000000)
  rootU := (303692816841/500000000000)
  rootV := (34123677/2000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_152.scalar_checked
  centre := fun n hn => lowFull3_152 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy152 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_152.bound (by norm_num) hn lowTIParameters152_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_153 : FrameRectangleCertificate 9000 10000 (1073/2000) (537/1000) lowTIParameters153 where
  full := (114157962721/1000000000000)
  energy := (167951831357/250000000000)
  cov := (62400450063/200000000000)
  schur := (126798848371/125000000000)
  cap := (482431501/500000000000)
  W2 := (646393954459/200000000000)
  V := (291377081/1000000000000)
  mass := (3776441/500000000000)
  rootN := (62948105703/62500000000)
  rootB := (6212448799/200000000000)
  rootU := (607416730739/1000000000000)
  rootV := (17069770971/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_153.scalar_checked
  centre := fun n hn => lowFull3_153 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy153 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_153.bound (by norm_num) hn lowTIParameters153_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_154 : FrameRectangleCertificate 9000 10000 (537/1000) (43/80) lowTIParameters154 where
  full := (114255423799/1000000000000)
  energy := (13431546877/20000000000)
  cov := (39036520343/125000000000)
  schur := (40583280623/40000000000)
  cap := (120707757/125000000000)
  W2 := (1614776275599/500000000000)
  V := (72911957/250000000000)
  mass := (7552843/1000000000000)
  rootN := (1007264620433/1000000000000)
  rootB := (7768775869/250000000000)
  rootU := (607448677189/1000000000000)
  rootV := (17077699729/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_154.scalar_checked
  centre := fun n hn => lowFull3_154 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy154 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_154.bound (by norm_num) hn lowTIParameters154_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_155 : FrameRectangleCertificate 9000 10000 (43/80) (269/500) lowTIParameters155 where
  full := (57176593393/500000000000)
  energy := (671347467681/1000000000000)
  cov := (312582075351/1000000000000)
  schur := (507386657799/500000000000)
  cap := (966461669/1000000000000)
  W2 := (1613570021929/500000000000)
  V := (18244911/62500000000)
  mass := (3776403/500000000000)
  rootN := (1007359576119/1000000000000)
  rootB := (31087966627/1000000000000)
  rootU := (121496295947/200000000000)
  rootV := (3417124967/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_155.scalar_checked
  centre := fun n hn => lowFull3_155 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy155 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_155.bound (by norm_num) hn lowTIParameters155_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_156 : FrameRectangleCertificate 9000 10000 (269/500) (1077/2000) lowTIParameters156 where
  full := (114451255013/1000000000000)
  energy := (33555884843/50000000000)
  cov := (312871988141/1000000000000)
  schur := (6343529293/6250000000)
  cap := (120907731/125000000000)
  W2 := (3224732236611/1000000000000)
  V := (73047331/250000000000)
  mass := (755277/100000000000)
  rootN := (1007454558221/1000000000000)
  rootB := (15550416779/500000000000)
  rootU := (607515145129/1000000000000)
  rootV := (4273386567/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_156.scalar_checked
  centre := fun n hn => lowFull3_156 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy156 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_156.bound (by norm_num) hn lowTIParameters156_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_157 : FrameRectangleCertificate 9000 10000 (1077/2000) (539/1000) lowTIParameters157 where
  full := (22909926369/200000000000)
  energy := (670888031319/1000000000000)
  cov := (39145237639/125000000000)
  schur := (1015156129227/1000000000000)
  cap := (968062599/1000000000000)
  W2 := (1611164557909/500000000000)
  V := (36557509/125000000000)
  mass := (7552737/1000000000000)
  rootN := (251887391659/250000000000)
  rootB := (777842609/25000000000)
  rootU := (9492963753/15625000000)
  rootV := (17101464031/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_157.scalar_checked
  centre := fun n hn => lowFull3_157 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy157 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_157.bound (by norm_num) hn lowTIParameters157_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_158 : FrameRectangleCertificate 9000 10000 (539/1000) (1079/2000) lowTIParameters158 where
  full := (57324160333/500000000000)
  energy := (670658470991/1000000000000)
  cov := (313451814261/1000000000000)
  schur := (1015347642433/1000000000000)
  cap := (968863929/1000000000000)
  W2 := (804982666959/250000000000)
  V := (14636541/50000000000)
  mass := (3776353/500000000000)
  rootN := (1007644601253/1000000000000)
  rootB := (31126579141/1000000000000)
  rootU := (7594813647/12500000000)
  rootV := (17109378131/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_158.scalar_checked
  centre := fun n hn => lowFull3_158 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy158 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_158.bound (by norm_num) hn lowTIParameters158_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle3_159 : FrameRectangleCertificate 9000 10000 (1079/2000) (27/50) lowTIParameters159 where
  full := (114747324899/1000000000000)
  energy := (670429015813/1000000000000)
  cov := (313741727591/1000000000000)
  schur := (507769613167/500000000000)
  cap := (969665843/1000000000000)
  W2 := (643507375829/200000000000)
  V := (9156299/31250000000)
  mass := (7552677/1000000000000)
  rootN := (31491864437/31250000000)
  rootB := (3892432247/125000000000)
  rootU := (607621386759/1000000000000)
  rootV := (17117288571/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness3_159.scalar_checked
  centre := fun n hn => lowFull3_159 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy159 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness3_159.bound (by norm_num) hn lowTIParameters159_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangles3 (j : Fin 160) :
    FrameRectangleCertificate 9000 10000 (frameNoiseLower j) (frameNoiseUpper j) (lowTIParameters j) := by
  match j with
  | ⟨0,_⟩ => convert lowRectangle3_0 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨1,_⟩ => convert lowRectangle3_1 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨2,_⟩ => convert lowRectangle3_2 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨3,_⟩ => convert lowRectangle3_3 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨4,_⟩ => convert lowRectangle3_4 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨5,_⟩ => convert lowRectangle3_5 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨6,_⟩ => convert lowRectangle3_6 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨7,_⟩ => convert lowRectangle3_7 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨8,_⟩ => convert lowRectangle3_8 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨9,_⟩ => convert lowRectangle3_9 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨10,_⟩ => convert lowRectangle3_10 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨11,_⟩ => convert lowRectangle3_11 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨12,_⟩ => convert lowRectangle3_12 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨13,_⟩ => convert lowRectangle3_13 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨14,_⟩ => convert lowRectangle3_14 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨15,_⟩ => convert lowRectangle3_15 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨16,_⟩ => convert lowRectangle3_16 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨17,_⟩ => convert lowRectangle3_17 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨18,_⟩ => convert lowRectangle3_18 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨19,_⟩ => convert lowRectangle3_19 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨20,_⟩ => convert lowRectangle3_20 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨21,_⟩ => convert lowRectangle3_21 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨22,_⟩ => convert lowRectangle3_22 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨23,_⟩ => convert lowRectangle3_23 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨24,_⟩ => convert lowRectangle3_24 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨25,_⟩ => convert lowRectangle3_25 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨26,_⟩ => convert lowRectangle3_26 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨27,_⟩ => convert lowRectangle3_27 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨28,_⟩ => convert lowRectangle3_28 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨29,_⟩ => convert lowRectangle3_29 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨30,_⟩ => convert lowRectangle3_30 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨31,_⟩ => convert lowRectangle3_31 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨32,_⟩ => convert lowRectangle3_32 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨33,_⟩ => convert lowRectangle3_33 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨34,_⟩ => convert lowRectangle3_34 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨35,_⟩ => convert lowRectangle3_35 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨36,_⟩ => convert lowRectangle3_36 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨37,_⟩ => convert lowRectangle3_37 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨38,_⟩ => convert lowRectangle3_38 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨39,_⟩ => convert lowRectangle3_39 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨40,_⟩ => convert lowRectangle3_40 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨41,_⟩ => convert lowRectangle3_41 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨42,_⟩ => convert lowRectangle3_42 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨43,_⟩ => convert lowRectangle3_43 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨44,_⟩ => convert lowRectangle3_44 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨45,_⟩ => convert lowRectangle3_45 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨46,_⟩ => convert lowRectangle3_46 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨47,_⟩ => convert lowRectangle3_47 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨48,_⟩ => convert lowRectangle3_48 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨49,_⟩ => convert lowRectangle3_49 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨50,_⟩ => convert lowRectangle3_50 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨51,_⟩ => convert lowRectangle3_51 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨52,_⟩ => convert lowRectangle3_52 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨53,_⟩ => convert lowRectangle3_53 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨54,_⟩ => convert lowRectangle3_54 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨55,_⟩ => convert lowRectangle3_55 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨56,_⟩ => convert lowRectangle3_56 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨57,_⟩ => convert lowRectangle3_57 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨58,_⟩ => convert lowRectangle3_58 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨59,_⟩ => convert lowRectangle3_59 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨60,_⟩ => convert lowRectangle3_60 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨61,_⟩ => convert lowRectangle3_61 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨62,_⟩ => convert lowRectangle3_62 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨63,_⟩ => convert lowRectangle3_63 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨64,_⟩ => convert lowRectangle3_64 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨65,_⟩ => convert lowRectangle3_65 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨66,_⟩ => convert lowRectangle3_66 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨67,_⟩ => convert lowRectangle3_67 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨68,_⟩ => convert lowRectangle3_68 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨69,_⟩ => convert lowRectangle3_69 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨70,_⟩ => convert lowRectangle3_70 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨71,_⟩ => convert lowRectangle3_71 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨72,_⟩ => convert lowRectangle3_72 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨73,_⟩ => convert lowRectangle3_73 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨74,_⟩ => convert lowRectangle3_74 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨75,_⟩ => convert lowRectangle3_75 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨76,_⟩ => convert lowRectangle3_76 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨77,_⟩ => convert lowRectangle3_77 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨78,_⟩ => convert lowRectangle3_78 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨79,_⟩ => convert lowRectangle3_79 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨80,_⟩ => convert lowRectangle3_80 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨81,_⟩ => convert lowRectangle3_81 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨82,_⟩ => convert lowRectangle3_82 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨83,_⟩ => convert lowRectangle3_83 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨84,_⟩ => convert lowRectangle3_84 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨85,_⟩ => convert lowRectangle3_85 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨86,_⟩ => convert lowRectangle3_86 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨87,_⟩ => convert lowRectangle3_87 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨88,_⟩ => convert lowRectangle3_88 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨89,_⟩ => convert lowRectangle3_89 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨90,_⟩ => convert lowRectangle3_90 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨91,_⟩ => convert lowRectangle3_91 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨92,_⟩ => convert lowRectangle3_92 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨93,_⟩ => convert lowRectangle3_93 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨94,_⟩ => convert lowRectangle3_94 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨95,_⟩ => convert lowRectangle3_95 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨96,_⟩ => convert lowRectangle3_96 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨97,_⟩ => convert lowRectangle3_97 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨98,_⟩ => convert lowRectangle3_98 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨99,_⟩ => convert lowRectangle3_99 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨100,_⟩ => convert lowRectangle3_100 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨101,_⟩ => convert lowRectangle3_101 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨102,_⟩ => convert lowRectangle3_102 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨103,_⟩ => convert lowRectangle3_103 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨104,_⟩ => convert lowRectangle3_104 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨105,_⟩ => convert lowRectangle3_105 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨106,_⟩ => convert lowRectangle3_106 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨107,_⟩ => convert lowRectangle3_107 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨108,_⟩ => convert lowRectangle3_108 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨109,_⟩ => convert lowRectangle3_109 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨110,_⟩ => convert lowRectangle3_110 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨111,_⟩ => convert lowRectangle3_111 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨112,_⟩ => convert lowRectangle3_112 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨113,_⟩ => convert lowRectangle3_113 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨114,_⟩ => convert lowRectangle3_114 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨115,_⟩ => convert lowRectangle3_115 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨116,_⟩ => convert lowRectangle3_116 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨117,_⟩ => convert lowRectangle3_117 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨118,_⟩ => convert lowRectangle3_118 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨119,_⟩ => convert lowRectangle3_119 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨120,_⟩ => convert lowRectangle3_120 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨121,_⟩ => convert lowRectangle3_121 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨122,_⟩ => convert lowRectangle3_122 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨123,_⟩ => convert lowRectangle3_123 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨124,_⟩ => convert lowRectangle3_124 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨125,_⟩ => convert lowRectangle3_125 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨126,_⟩ => convert lowRectangle3_126 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨127,_⟩ => convert lowRectangle3_127 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨128,_⟩ => convert lowRectangle3_128 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨129,_⟩ => convert lowRectangle3_129 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨130,_⟩ => convert lowRectangle3_130 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨131,_⟩ => convert lowRectangle3_131 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨132,_⟩ => convert lowRectangle3_132 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨133,_⟩ => convert lowRectangle3_133 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨134,_⟩ => convert lowRectangle3_134 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨135,_⟩ => convert lowRectangle3_135 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨136,_⟩ => convert lowRectangle3_136 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨137,_⟩ => convert lowRectangle3_137 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨138,_⟩ => convert lowRectangle3_138 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨139,_⟩ => convert lowRectangle3_139 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨140,_⟩ => convert lowRectangle3_140 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨141,_⟩ => convert lowRectangle3_141 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨142,_⟩ => convert lowRectangle3_142 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨143,_⟩ => convert lowRectangle3_143 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨144,_⟩ => convert lowRectangle3_144 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨145,_⟩ => convert lowRectangle3_145 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨146,_⟩ => convert lowRectangle3_146 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨147,_⟩ => convert lowRectangle3_147 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨148,_⟩ => convert lowRectangle3_148 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨149,_⟩ => convert lowRectangle3_149 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨150,_⟩ => convert lowRectangle3_150 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨151,_⟩ => convert lowRectangle3_151 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨152,_⟩ => convert lowRectangle3_152 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨153,_⟩ => convert lowRectangle3_153 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨154,_⟩ => convert lowRectangle3_154 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨155,_⟩ => convert lowRectangle3_155 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨156,_⟩ => convert lowRectangle3_156 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨157,_⟩ => convert lowRectangle3_157 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨158,_⟩ => convert lowRectangle3_158 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨159,_⟩ => convert lowRectangle3_159 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨j+160,h⟩ => exact False.elim (by omega)
end BstLean.BlueprintLow
