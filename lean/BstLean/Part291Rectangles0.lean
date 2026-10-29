import BstLean.Part291Rectangle
import BstLean.Part291Certificates0
import BstLean.Part291LocalEnergyBatch0
import BstLean.Part291LocalEnergyBatch1
namespace BstLean.BlueprintLow
open Real Set BstLean.Part255
noncomputable def lowRectangle0_0 : FrameRectangleCertificate 8000 8250 (23/50) (921/2000) lowTIParameters0 where
  full := (11257206203/100000000000)
  energy := (44267434443/62500000000)
  cov := (56898615869/200000000000)
  schur := (262682266731/250000000000)
  cap := (1007192531/1000000000000)
  W2 := (22971596009/6250000000)
  V := (29889723/100000000000)
  mass := (494151903/1000000000000)
  rootN := (1025050763097/1000000000000)
  rootB := (3967037093/125000000000)
  rootU := (643236806267/1000000000000)
  rootV := (864432227/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_0.scalar_checked
  centre := fun n hn => lowFull0_0 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy0 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_0.bound (by norm_num) hn lowTIParameters0_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_1 : FrameRectangleCertificate 8000 8250 (921/2000) (461/1000) lowTIParameters1 where
  full := (112659837121/1000000000000)
  energy := (708032000171/1000000000000)
  cov := (3558442321/12500000000)
  schur := (1050451217187/1000000000000)
  cap := (503908351/500000000000)
  W2 := (3672098984107/1000000000000)
  V := (149544383/500000000000)
  mass := (5917461/12500000000)
  rootN := (1024915224391/1000000000000)
  rootB := (3174612893/100000000000)
  rootU := (643193651587/1000000000000)
  rootV := (17294183011/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_1.scalar_checked
  centre := fun n hn => lowFull0_1 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy1 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_1.bound (by norm_num) hn lowTIParameters1_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_2 : FrameRectangleCertificate 8000 8250 (461/1000) (923/2000) lowTIParameters2 where
  full := (563739117/5000000000)
  energy := (353892583027/500000000000)
  cov := (284857504151/1000000000000)
  schur := (131271705217/125000000000)
  cap := (100844089/100000000000)
  W2 := (733750061171/200000000000)
  V := (149640053/500000000000)
  mass := (454641527/1000000000000)
  rootN := (204955960317/200000000000)
  rootB := (31755958339/1000000000000)
  rootU := (160787828283/250000000000)
  rootV := (4324928511/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_2.scalar_checked
  centre := fun n hn => lowFull0_2 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy2 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_2.bound (by norm_num) hn lowTIParameters2_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_3 : FrameRectangleCertificate 8000 8250 (923/2000) (231/500) lowTIParameters3 where
  full := (112836023749/1000000000000)
  energy := (707538448651/1000000000000)
  cov := (8911419363/31250000000)
  schur := (525180036607/500000000000)
  cap := (100935621/100000000000)
  W2 := (3665409300147/1000000000000)
  V := (299603611/1000000000000)
  mass := (21884289/50000000000)
  rootN := (512435379637/500000000000)
  rootB := (15885183427/500000000000)
  rootU := (643109796879/1000000000000)
  rootV := (17309061529/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_3.scalar_checked
  centre := fun n hn => lowFull0_3 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy3 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_3.bound (by norm_num) hn lowTIParameters3_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_4 : FrameRectangleCertificate 8000 8250 (231/500) (37/80) lowTIParameters4 where
  full := (112924441083/1000000000000)
  energy := (707291847877/1000000000000)
  cov := (285221176763/1000000000000)
  schur := (1049619305111/1000000000000)
  cap := (504844669/500000000000)
  W2 := (1831037970319/500000000000)
  V := (299662191/1000000000000)
  mass := (422350327/1000000000000)
  rootN := (1024509299671/1000000000000)
  rootB := (31775609169/1000000000000)
  rootU := (160767277221/250000000000)
  rootV := (2163844203/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_4.scalar_checked
  centre := fun n hn => lowFull0_4 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy4 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_4.bound (by norm_num) hn lowTIParameters4_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_5 : FrameRectangleCertificate 8000 8250 (37/80) (463/1000) lowTIParameters5 where
  full := (56506539173/500000000000)
  energy := (176761340913/250000000000)
  cov := (142764410007/500000000000)
  schur := (524902910661/500000000000)
  cap := (7895351/7812500000)
  W2 := (731750040229/200000000000)
  V := (299985411/1000000000000)
  mass := (51059297/125000000000)
  rootN := (512300161361/500000000000)
  rootB := (31790013023/1000000000000)
  rootU := (160757313817/250000000000)
  rootV := (17320086923/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_5.scalar_checked
  centre := fun n hn => lowFull0_5 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy5 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_5.bound (by norm_num) hn lowTIParameters5_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_6 : FrameRectangleCertificate 8000 8250 (463/1000) (927/2000) lowTIParameters6 where
  full := (113101938511/1000000000000)
  energy := (44174937243/62500000000)
  cov := (285584099821/1000000000000)
  schur := (1049066055209/1000000000000)
  cap := (63183621/62500000000)
  W2 := (913858013879/250000000000)
  V := (30004349/100000000000)
  mass := (395913677/1000000000000)
  rootN := (1024239256819/1000000000000)
  rootB := (7948812553/250000000000)
  rootU := (20093445069/31250000000)
  rootV := (17321763479/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_6.scalar_checked
  centre := fun n hn => lowFull0_6 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy6 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_6.bound (by norm_num) hn lowTIParameters6_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_7 : FrameRectangleCertificate 8000 8250 (927/2000) (58/125) lowTIParameters7 where
  full := (113191024587/1000000000000)
  energy := (141310548901/200000000000)
  cov := (35736433903/125000000000)
  schur := (524626327107/500000000000)
  cap := (1976277/1953125000)
  W2 := (456515184723/125000000000)
  V := (300366423/1000000000000)
  mass := (384538759/1000000000000)
  rootN := (1024330344281/1000000000000)
  rootB := (31809649857/1000000000000)
  rootU := (128590415193/200000000000)
  rootV := (17331082569/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_7.scalar_checked
  centre := fun n hn => lowFull0_7 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy7 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_7.bound (by norm_num) hn lowTIParameters7_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_8 : FrameRectangleCertificate 8000 8250 (58/125) (929/2000) lowTIParameters8 where
  full := (113280339611/1000000000000)
  energy := (35315330471/50000000000)
  cov := (142973136839/500000000000)
  schur := (209702776377/200000000000)
  cap := (506093371/500000000000)
  W2 := (1824409221073/500000000000)
  V := (300424001/1000000000000)
  mass := (93558341/250000000000)
  rootN := (25599241711/25000000000)
  rootB := (31814882399/1000000000000)
  rootU := (321457381431/500000000000)
  rootV := (17332743609/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_8.scalar_checked
  centre := fun n hn => lowFull0_8 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy8 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_8.bound (by norm_num) hn lowTIParameters8_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_9 : FrameRectangleCertificate 8000 8250 (929/2000) (93/200) lowTIParameters9 where
  full := (113369886651/1000000000000)
  energy := (353030295273/500000000000)
  cov := (143126686797/500000000000)
  schur := (1048700561771/1000000000000)
  cap := (1013102957/1000000000000)
  W2 := (3645522922757/1000000000000)
  V := (300746649/1000000000000)
  mass := (364893051/1000000000000)
  rootN := (256015204843/250000000000)
  rootB := (31829278299/1000000000000)
  rootU := (160719577319/250000000000)
  rootV := (8671024291/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_9.scalar_checked
  centre := fun n hn => lowFull0_9 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy9 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_9.bound (by norm_num) hn lowTIParameters9_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_10 : FrameRectangleCertificate 8000 8250 (93/200) (931/2000) lowTIParameters10 where
  full := (11345966881/100000000000)
  energy := (705814687803/1000000000000)
  cov := (286307699121/1000000000000)
  schur := (1047962776631/1000000000000)
  cap := (1013435811/1000000000000)
  W2 := (3642234894027/1000000000000)
  V := (12032149/40000000000)
  mass := (356423953/1000000000000)
  rootN := (1023700530737/1000000000000)
  rootB := (31834506609/1000000000000)
  rootU := (642842721671/1000000000000)
  rootV := (173436941/10000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_10.scalar_checked
  centre := fun n hn => lowFull0_10 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy10 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_10.bound (by norm_num) hn lowTIParameters10_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_11 : FrameRectangleCertificate 8000 8250 (931/2000) (233/500) lowTIParameters11 where
  full := (56774844611/500000000000)
  energy := (705568901107/1000000000000)
  cov := (286614527911/1000000000000)
  schur := (1048149535513/1000000000000)
  cap := (1014352383/1000000000000)
  W2 := (3638954330477/1000000000000)
  V := (301126089/1000000000000)
  mass := (348741669/1000000000000)
  rootN := (1023791744211/1000000000000)
  rootB := (7962224811/250000000000)
  rootU := (642808006577/1000000000000)
  rootV := (17352985017/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_11.scalar_checked
  centre := fun n hn => lowFull0_11 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy11 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_11.bound (by norm_num) hn lowTIParameters11_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_12 : FrameRectangleCertificate 8000 8250 (233/500) (933/2000) lowTIParameters12 where
  full := (22727990211/200000000000)
  energy := (88165403797/125000000000)
  cov := (286668377403/1000000000000)
  schur := (1047412732793/1000000000000)
  cap := (507342603/500000000000)
  W2 := (28403759427/7812500000)
  V := (60236533/200000000000)
  mass := (170885137/500000000000)
  rootN := (204686368163/200000000000)
  rootB := (31854123847/1000000000000)
  rootU := (642774170589/1000000000000)
  rootV := (17354615093/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_12.scalar_checked
  centre := fun n hn => lowFull0_12 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy12 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_12.bound (by norm_num) hn lowTIParameters12_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_13 : FrameRectangleCertificate 8000 8250 (933/2000) (467/1000) lowTIParameters13 where
  full := (22746091501/200000000000)
  energy := (352538837763/500000000000)
  cov := (71743733857/250000000000)
  schur := (1047599568781/1000000000000)
  cap := (203120433/200000000000)
  W2 := (1816207748659/500000000000)
  V := (37688093/125000000000)
  mass := (167720721/500000000000)
  rootN := (10235231159/10000000000)
  rootB := (31868513693/1000000000000)
  rootU := (642741220367/1000000000000)
  rootV := (17363891961/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_13.scalar_checked
  centre := fun n hn => lowFull0_13 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy13 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_13.bound (by norm_num) hn lowTIParameters13_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_14 : FrameRectangleCertificate 8000 8250 (467/1000) (187/400) lowTIParameters14 where
  full := (56910605903/500000000000)
  energy := (704832236477/1000000000000)
  cov := (1148113239/4000000000)
  schur := (1046863743627/1000000000000)
  cap := (253983747/250000000000)
  W2 := (3629157177329/1000000000000)
  V := (301560821/1000000000000)
  mass := (329693653/1000000000000)
  rootN := (102316359573/100000000000)
  rootB := (31873735081/1000000000000)
  rootU := (642709162653/1000000000000)
  rootV := (4341376661/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_14.scalar_checked
  centre := fun n hn => lowFull0_14 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy14 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_14.bound (by norm_num) hn lowTIParameters14_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_15 : FrameRectangleCertificate 8000 8250 (187/400) (117/250) lowTIParameters15 where
  full := (56956108611/500000000000)
  energy := (88073364143/125000000000)
  cov := (287334597369/1000000000000)
  schur := (1047050654897/1000000000000)
  cap := (254213091/250000000000)
  W2 := (3625906221581/1000000000000)
  V := (37735327/125000000000)
  mass := (324471497/1000000000000)
  rootN := (1023254931529/1000000000000)
  rootB := (31888122617/1000000000000)
  rootU := (128535600849/200000000000)
  rootV := (4343692381/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_15.scalar_checked
  centre := fun n hn => lowFull0_15 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy15 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_15.bound (by norm_num) hn lowTIParameters15_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_16 : FrameRectangleCertificate 8000 8250 (117/250) (937/2000) lowTIParameters16 where
  full := (114003477053/1000000000000)
  energy := (140868341089/200000000000)
  cov := (287387496937/1000000000000)
  schur := (1046315800853/1000000000000)
  cap := (508592609/500000000000)
  W2 := (3622662605141/1000000000000)
  V := (150969097/500000000000)
  mass := (319725041/1000000000000)
  rootN := (511447895893/500000000000)
  rootB := (199333383/6250000000)
  rootU := (32132387601/50000000000)
  rootV := (17376368839/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_16.scalar_checked
  centre := fun n hn => lowFull0_16 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy16 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_16.bound (by norm_num) hn lowTIParameters16_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_17 : FrameRectangleCertificate 8000 8250 (937/2000) (469/1000) lowTIParameters17 where
  full := (114094994629/1000000000000)
  energy := (704096613301/1000000000000)
  cov := (287693514509/1000000000000)
  schur := (261625696393/250000000000)
  cap := (1018103043/1000000000000)
  W2 := (90485657581/25000000000)
  V := (151129853/500000000000)
  mass := (39426159/125000000000)
  rootN := (511493593697/500000000000)
  rootB := (31907727011/1000000000000)
  rootU := (160654603231/250000000000)
  rootV := (135825139/7812500000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_17.scalar_checked
  centre := fun n hn => lowFull0_17 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy17 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_17.bound (by norm_num) hn lowTIParameters17_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_18 : FrameRectangleCertificate 8000 8250 (469/1000) (939/2000) lowTIParameters18 where
  full := (114186773319/1000000000000)
  energy := (703851636627/1000000000000)
  cov := (143872970087/500000000000)
  schur := (1045768897853/1000000000000)
  cap := (509217981/500000000000)
  W2 := (3616197291101/1000000000000)
  V := (151157393/500000000000)
  mass := (311483593/1000000000000)
  rootN := (1022628426093/1000000000000)
  rootB := (31912943487/1000000000000)
  rootU := (25703599759/40000000000)
  rootV := (4346800447/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_18.scalar_checked
  centre := fun n hn => lowFull0_18 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy18 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_18.bound (by norm_num) hn lowTIParameters18_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_19 : FrameRectangleCertificate 8000 8250 (939/2000) (47/100) lowTIParameters19 where
  full := (114278816521/1000000000000)
  energy := (351803387671/500000000000)
  cov := (144025844027/500000000000)
  schur := (522977977103/500000000000)
  cap := (254838567/250000000000)
  W2 := (1806487772099/500000000000)
  V := (151318007/500000000000)
  mass := (19244461/62500000000)
  rootN := (127839985077/125000000000)
  rootB := (31927327919/1000000000000)
  rootU := (32128125113/50000000000)
  rootV := (869821841/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_19.scalar_checked
  centre := fun n hn => lowFull0_19 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy19 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_19.bound (by norm_num) hn lowTIParameters19_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_20 : FrameRectangleCertificate 8000 8250 (47/100) (941/2000) lowTIParameters20 where
  full := (114371127669/1000000000000)
  energy := (703362029363/1000000000000)
  cov := (18006477513/62500000000)
  schur := (1045223026397/1000000000000)
  cap := (509843641/500000000000)
  W2 := (3609761037953/1000000000000)
  V := (302690597/1000000000000)
  mass := (152329779/500000000000)
  rootN := (102236149497/100000000000)
  rootB := (798313567/25000000000)
  rootU := (64253594493/100000000000)
  rootV := (17398005547/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_20.scalar_checked
  centre := fun n hn => lowFull0_20 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy20 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_20.bound (by norm_num) hn lowTIParameters20_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_21 : FrameRectangleCertificate 8000 8250 (941/2000) (471/1000) lowTIParameters21 where
  full := (57231855117/500000000000)
  energy := (175779349653/250000000000)
  cov := (288409118753/1000000000000)
  schur := (104541015261/100000000000)
  cap := (1020606103/1000000000000)
  W2 := (1803276874051/500000000000)
  V := (151505771/500000000000)
  mass := (150849143/500000000000)
  rootN := (255613251883/250000000000)
  rootB := (31946926347/1000000000000)
  rootU := (64251032923/100000000000)
  rootV := (8703613359/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_21.scalar_checked
  centre := fun n hn => lowFull0_21 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy21 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_21.bound (by norm_num) hn lowTIParameters21_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_22 : FrameRectangleCertificate 8000 8250 (471/1000) (943/2000) lowTIParameters22 where
  full := (57278283859/500000000000)
  energy := (702872883003/1000000000000)
  cov := (72178649393/250000000000)
  schur := (1045597395873/1000000000000)
  cap := (1021525477/1000000000000)
  W2 := (3603353650267/1000000000000)
  V := (303332487/1000000000000)
  mass := (74750147/250000000000)
  rootN := (511272284569/500000000000)
  rootB := (499395503/15625000000)
  rootU := (642485662447/1000000000000)
  rootV := (17416443007/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_22.scalar_checked
  centre := fun n hn => lowFull0_22 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy22 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_22.bound (by norm_num) hn lowTIParameters22_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_23 : FrameRectangleCertificate 8000 8250 (943/2000) (59/125) lowTIParameters23 where
  full := (7165606479/62500000000)
  energy := (702628482457/1000000000000)
  cov := (289020076659/1000000000000)
  schur := (209156951159/200000000000)
  cap := (1022445413/1000000000000)
  W2 := (3600160720333/1000000000000)
  V := (303653433/1000000000000)
  mass := (296542091/1000000000000)
  rootN := (204527235917/200000000000)
  rootB := (249810159/7812500000)
  rootU := (64246195197/100000000000)
  rootV := (348513089/20000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_23.scalar_checked
  centre := fun n hn => lowFull0_23 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy23 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_23.bound (by norm_num) hn lowTIParameters23_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_24 : FrameRectangleCertificate 8000 8250 (59/125) (189/400) lowTIParameters24 where
  full := (114743121643/1000000000000)
  energy := (140476839379/200000000000)
  cov := (57865111203/200000000000)
  schur := (261493058001/250000000000)
  cap := (511682961/500000000000)
  W2 := (3596974934311/1000000000000)
  V := (303974379/1000000000000)
  mass := (7357519/25000000000)
  rootN := (1022727838677/1000000000000)
  rootB := (15995045499/500000000000)
  rootU := (160609801311/250000000000)
  rootV := (17434861027/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_24.scalar_checked
  centre := fun n hn => lowFull0_24 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy24 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_24.bound (by norm_num) hn lowTIParameters24_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_25 : FrameRectangleCertificate 8000 8250 (189/400) (473/1000) lowTIParameters25 where
  full := (114836825263/1000000000000)
  energy := (351070013117/500000000000)
  cov := (144815517821/500000000000)
  schur := (1046159824109/1000000000000)
  cap := (1024287007/1000000000000)
  W2 := (718759253639/200000000000)
  V := (152147663/500000000000)
  mass := (36532083/125000000000)
  rootN := (102281954621/100000000000)
  rootB := (32004484171/1000000000000)
  rootU := (321208714889/500000000000)
  rootV := (17444062773/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_25.scalar_checked
  centre := fun n hn => lowFull0_25 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy25 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_25.bound (by norm_num) hn lowTIParameters25_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_26 : FrameRectangleCertificate 8000 8250 (473/1000) (947/2000) lowTIParameters26 where
  full := (57465409087/500000000000)
  energy := (350947985197/500000000000)
  cov := (289936515539/1000000000000)
  schur := (523173765861/500000000000)
  cap := (1025208681/1000000000000)
  W2 := (718124939637/200000000000)
  V := (19038517/62500000000)
  mass := (36298971/125000000000)
  rootN := (511455650991/500000000000)
  rootB := (32018880071/1000000000000)
  rootU := (321198316589/500000000000)
  rootV := (17453259639/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_26.scalar_checked
  centre := fun n hn => lowFull0_26 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy26 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_26.bound (by norm_num) hn lowTIParameters26_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_27 : FrameRectangleCertificate 8000 8250 (947/2000) (237/500) lowTIParameters27 where
  full := (23005020811/200000000000)
  energy := (701652029291/1000000000000)
  cov := (58048399141/200000000000)
  schur := (52326767723/50000000000)
  cap := (1026130951/1000000000000)
  W2 := (896865050127/250000000000)
  V := (304937219/1000000000000)
  mass := (1154759/4000000000)
  rootN := (1998052941/1953125000)
  rootB := (16016639403/500000000000)
  rootU := (642376823101/1000000000000)
  rootV := (1746245169/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_27.scalar_checked
  centre := fun n hn => lowFull0_27 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy27 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_27.bound (by norm_num) hn lowTIParameters27_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_28 : FrameRectangleCertificate 8000 8250 (237/500) (949/2000) lowTIParameters28 where
  full := (57559843313/500000000000)
  energy := (701408202847/1000000000000)
  cov := (145273738069/500000000000)
  schur := (1046723291919/1000000000000)
  cap := (4011929/3906250000)
  W2 := (3584302751557/1000000000000)
  V := (152629083/500000000000)
  mass := (287135829/1000000000000)
  rootN := (1023094957431/1000000000000)
  rootB := (16023840239/500000000000)
  rootU := (160589501823/250000000000)
  rootV := (3494327781/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_28.scalar_checked
  centre := fun n hn => lowFull0_28 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy28 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_28.bound (by norm_num) hn lowTIParameters28_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_29 : FrameRectangleCertificate 8000 8250 (949/2000) (19/40) lowTIParameters29 where
  full := (115214569639/1000000000000)
  energy := (87645561373/125000000000)
  cov := (7271323921/25000000000)
  schur := (523455671883/500000000000)
  cap := (1027977309/1000000000000)
  W2 := (716230465579/200000000000)
  V := (152789557/500000000000)
  mass := (142858307/500000000000)
  rootN := (1023186856721/1000000000000)
  rootB := (16031042613/500000000000)
  rootU := (321170096783/500000000000)
  rootV := (437020533/25000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_29.scalar_checked
  centre := fun n hn => lowFull0_29 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy29 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_29.bound (by norm_num) hn lowTIParameters29_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_30 : FrameRectangleCertificate 8000 8250 (19/40) (951/2000) lowTIParameters30 where
  full := (14413719611/125000000000)
  energy := (350460446809/500000000000)
  cov := (291158437811/1000000000000)
  schur := (523549754799/500000000000)
  cap := (128612677/125000000000)
  W2 := (89450222651/25000000000)
  V := (152950031/500000000000)
  mass := (284419971/1000000000000)
  rootN := (511639401727/500000000000)
  rootB := (80191233/2500000000)
  rootU := (160580847453/250000000000)
  rootV := (8744999457/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_30.scalar_checked
  centre := fun n hn => lowFull0_30 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy30 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_30.bound (by norm_num) hn lowTIParameters30_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_31 : FrameRectangleCertificate 8000 8250 (951/2000) (119/250) lowTIParameters31 where
  full := (57702626099/500000000000)
  energy := (700677410671/1000000000000)
  cov := (291463919047/1000000000000)
  schur := (1047287789039/1000000000000)
  cap := (514913077/500000000000)
  W2 := (1787436231369/500000000000)
  V := (30622101/100000000000)
  mass := (2832349/10000000000)
  rootN := (511685398717/500000000000)
  rootB := (32090904537/1000000000000)
  rootU := (321153801993/500000000000)
  rootV := (3499834339/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_31.scalar_checked
  centre := fun n hn => lowFull0_31 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy31 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_31.bound (by norm_num) hn lowTIParameters31_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_32 : FrameRectangleCertificate 8000 8250 (119/250) (953/2000) lowTIParameters32 where
  full := (57750529719/500000000000)
  energy := (350217021031/500000000000)
  cov := (291769400551/1000000000000)
  schur := (1047476181711/1000000000000)
  cap := (1030751531/1000000000000)
  W2 := (714348594947/200000000000)
  V := (153270979/500000000000)
  mass := (11286057/40000000000)
  rootN := (511731419231/500000000000)
  rootB := (32105319357/1000000000000)
  rootU := (160573211033/250000000000)
  rootV := (1750833967/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_32.scalar_checked
  centre := fun n hn => lowFull0_32 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy32 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_32.bound (by norm_num) hn lowTIParameters32_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_33 : FrameRectangleCertificate 8000 8250 (953/2000) (477/1000) lowTIParameters33 where
  full := (28899295627/250000000000)
  energy := (700190787709/1000000000000)
  cov := (292074882321/1000000000000)
  schur := (261916171811/250000000000)
  cap := (206335511/200000000000)
  W2 := (1784310209471/500000000000)
  V := (153431453/500000000000)
  mass := (140580247/500000000000)
  rootN := (204710985269/200000000000)
  rootB := (1605986889/50000000000)
  rootU := (40142444897/62500000000)
  rootV := (136855491/7812500000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_33.scalar_checked
  centre := fun n hn => lowFull0_33 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy33 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_33.bound (by norm_num) hn lowTIParameters33_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_34 : FrameRectangleCertificate 8000 8250 (477/1000) (191/400) lowTIParameters34 where
  full := (115693625351/1000000000000)
  energy := (349973823769/500000000000)
  cov := (58476072871/200000000000)
  schur := (1047853305269/1000000000000)
  cap := (206520847/200000000000)
  W2 := (1782752386207/500000000000)
  V := (61436771/200000000000)
  mass := (140126947/500000000000)
  rootN := (1023647060891/1000000000000)
  rootB := (1606707997/50000000000)
  rootU := (160566608711/250000000000)
  rootV := (17526661263/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_34.scalar_checked
  centre := fun n hn => lowFull0_34 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy34 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_34.bound (by norm_num) hn lowTIParameters34_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_35 : FrameRectangleCertificate 8000 8250 (191/400) (239/500) lowTIParameters35 where
  full := (14473798993/125000000000)
  energy := (349852310731/500000000000)
  cov := (146342923329/500000000000)
  schur := (1048042035429/1000000000000)
  cap := (1033531583/1000000000000)
  W2 := (17811980061/5000000000)
  V := (76876201/250000000000)
  mass := (55884833/200000000000)
  rootN := (127967405239/125000000000)
  rootB := (32148586019/1000000000000)
  rootU := (642254801861/1000000000000)
  rootV := (3507162979/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_35.scalar_checked
  centre := fun n hn => lowFull0_35 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy35 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_35.bound (by norm_num) hn lowTIParameters35_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_36 : FrameRectangleCertificate 8000 8250 (239/500) (957/2000) lowTIParameters36 where
  full := (57943743153/500000000000)
  energy := (699461709407/1000000000000)
  cov := (11719653169/40000000000)
  schur := (1048230877343/1000000000000)
  cap := (258614901/250000000000)
  W2 := (1779647057779/500000000000)
  V := (153912877/500000000000)
  mass := (139332267/500000000000)
  rootN := (102383146921/100000000000)
  rootB := (3216301609/100000000000)
  rootU := (642244227749/1000000000000)
  rootV := (17544963779/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_36.scalar_checked
  centre := fun n hn => lowFull0_36 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy36 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_36.bound (by norm_num) hn lowTIParameters36_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_37 : FrameRectangleCertificate 8000 8250 (957/2000) (479/1000) lowTIParameters37 where
  full := (115984912491/1000000000000)
  energy := (699218911291/1000000000000)
  cov := (293296812053/1000000000000)
  schur := (209683966127/200000000000)
  cap := (1035388311/1000000000000)
  W2 := (177809952989/50000000000)
  V := (19259169/62500000000)
  mass := (138984423/500000000000)
  rootN := (255980935647/250000000000)
  rootB := (643549007/20000000000)
  rootU := (160558680229/250000000000)
  rootV := (2194263487/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_37.scalar_checked
  centre := fun n hn => lowFull0_37 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy37 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_37.bound (by norm_num) hn lowTIParameters37_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_38 : FrameRectangleCertificate 8000 8250 (479/1000) (959/2000) lowTIParameters38 where
  full := (3627583581/31250000000)
  energy := (349488113519/500000000000)
  cov := (293602295149/1000000000000)
  schur := (209721778997/200000000000)
  cap := (1036317709/1000000000000)
  W2 := (1776555411161/500000000000)
  V := (154233827/500000000000)
  mass := (277331507/1000000000000)
  rootN := (1024016061879/1000000000000)
  rootB := (3219188887/100000000000)
  rootU := (160556572463/250000000000)
  rootV := (4390811813/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_38.scalar_checked
  centre := fun n hn => lowFull0_38 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy38 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_38.bound (by norm_num) hn lowTIParameters38_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_39 : FrameRectangleCertificate 8000 8250 (959/2000) (12/25) lowTIParameters39 where
  full := (116180776743/1000000000000)
  energy := (139746731313/200000000000)
  cov := (293907778507/1000000000000)
  schur := (262199517499/250000000000)
  cap := (1037247813/1000000000000)
  W2 := (1775014690317/500000000000)
  V := (77197151/250000000000)
  mass := (276747431/1000000000000)
  rootN := (1638573483/1600000000)
  rootB := (16103165939/500000000000)
  rootU := (642218943121/1000000000000)
  rootV := (8786190927/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_39.scalar_checked
  centre := fun n hn => lowFull0_39 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy39 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_39.bound (by norm_num) hn lowTIParameters39_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_40 : FrameRectangleCertificate 8000 8250 (12/25) (961/2000) lowTIParameters40 where
  full := (58139611559/500000000000)
  energy := (698491199793/1000000000000)
  cov := (7290999881/25000000000)
  schur := (1039819531039/1000000000000)
  cap := (258061851/250000000000)
  W2 := (141878188493/40000000000)
  V := (306406001/1000000000000)
  mass := (276211991/1000000000000)
  rootN := (254928854173/250000000000)
  rootB := (32128607253/1000000000000)
  rootU := (642212689367/1000000000000)
  rootV := (4376114151/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_40.scalar_checked
  centre := fun n hn => lowFull0_40 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy40 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_40.bound (by norm_num) hn lowTIParameters40_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_41 : FrameRectangleCertificate 8000 8250 (961/2000) (481/1000) lowTIParameters41 where
  full := (4655120717/40000000000)
  energy := (698248856647/1000000000000)
  cov := (145971399859/500000000000)
  schur := (1040007261773/1000000000000)
  cap := (258293321/250000000000)
  W2 := (885971698787/250000000000)
  V := (38340517/125000000000)
  mass := (275720979/1000000000000)
  rootN := (101980746309/100000000000)
  rootB := (32143012989/1000000000000)
  rootU := (80275942163/125000000000)
  rootV := (136824543/7812500000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_41.scalar_checked
  centre := fun n hn => lowFull0_41 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy41 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_41.bound (by norm_num) hn lowTIParameters41_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_42 : FrameRectangleCertificate 8000 8250 (481/1000) (963/2000) lowTIParameters42 where
  full := (5823858271/50000000000)
  energy := (349003313523/500000000000)
  cov := (292245604459/1000000000000)
  schur := (520097550577/500000000000)
  cap := (517049949/500000000000)
  W2 := (3540825606927/1000000000000)
  V := (9595071/31250000000)
  mass := (275270561/1000000000000)
  rootN := (254974888611/250000000000)
  rootB := (6431484737/200000000000)
  rootU := (642203495741/1000000000000)
  rootV := (8761310861/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_42.scalar_checked
  centre := fun n hn => lowFull0_42 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy42 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_42.bound (by norm_num) hn lowTIParameters42_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_43 : FrameRectangleCertificate 8000 8250 (963/2000) (241/500) lowTIParameters43 where
  full := (29144167473/250000000000)
  energy := (697764510909/1000000000000)
  cov := (58509681891/200000000000)
  schur := (104038304879/100000000000)
  cap := (258756813/250000000000)
  W2 := (1768885562741/500000000000)
  V := (307360409/1000000000000)
  mass := (274857251/1000000000000)
  rootN := (20399833811/20000000000)
  rootB := (16085919713/500000000000)
  rootU := (20068767923/31250000000)
  rootV := (8765848633/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_43.scalar_checked
  centre := fun n hn => lowFull0_43 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy43 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_43.bound (by norm_num) hn lowTIParameters43_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_44 : FrameRectangleCertificate 8000 8250 (241/500) (193/400) lowTIParameters44 where
  full := (11667653567/100000000000)
  energy := (348761254081/500000000000)
  cov := (73212803679/250000000000)
  schur := (520285552197/500000000000)
  cap := (6474721/6250000000)
  W2 := (1767361664459/500000000000)
  V := (61535709/200000000000)
  mass := (27447787/100000000000)
  rootN := (204016774251/200000000000)
  rootB := (32186260423/1000000000000)
  rootU := (16054969491/25000000000)
  rootV := (3508153617/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_44.scalar_checked
  centre := fun n hn => lowFull0_44 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy44 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_44.bound (by norm_num) hn lowTIParameters44_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_45 : FrameRectangleCertificate 8000 8250 (193/400) (483/1000) lowTIParameters45 where
  full := (29194191783/250000000000)
  energy := (174320154681/250000000000)
  cov := (36644252529/125000000000)
  schur := (1040759267567/1000000000000)
  cap := (1036884231/1000000000000)
  W2 := (882920548821/250000000000)
  V := (153998341/500000000000)
  mass := (274129523/1000000000000)
  rootN := (31880503011/31250000000)
  rootB := (3220068681/100000000000)
  rootU := (642198123093/1000000000000)
  rootV := (3509966849/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_45.scalar_checked
  centre := fun n hn => lowFull0_45 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy45 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_45.bound (by norm_num) hn lowTIParameters45_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_46 : FrameRectangleCertificate 8000 8250 (483/1000) (967/2000) lowTIParameters46 where
  full := (58438684343/500000000000)
  energy := (348519421259/500000000000)
  cov := (293456826007/1000000000000)
  schur := (1040947537991/1000000000000)
  cap := (1037813873/1000000000000)
  W2 := (1764323851407/500000000000)
  V := (308314819/1000000000000)
  mass := (273809571/1000000000000)
  rootN := (127533545709/125000000000)
  rootB := (32215118703/1000000000000)
  rootU := (642198612989/1000000000000)
  rootV := (17558895723/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_46.scalar_checked
  centre := fun n hn => lowFull0_46 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy46 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_46.bound (by norm_num) hn lowTIParameters46_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_47 : FrameRectangleCertificate 8000 8250 (967/2000) (121/250) lowTIParameters47 where
  full := (58489172393/500000000000)
  energy := (87099647433/125000000000)
  cov := (146879816019/500000000000)
  schur := (520567957647/500000000000)
  cap := (519372149/500000000000)
  W2 := (3525619829729/1000000000000)
  V := (308632957/1000000000000)
  mass := (34189451/125000000000)
  rootN := (510180339511/500000000000)
  rootB := (805738907/25000000000)
  rootU := (642200258507/1000000000000)
  rootV := (4391988139/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_47.scalar_checked
  centre := fun n hn => lowFull0_47 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy47 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_47.bound (by norm_num) hn lowTIParameters47_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_48 : FrameRectangleCertificate 8000 8250 (121/250) (969/2000) lowTIParameters48 where
  full := (117079699929/1000000000000)
  energy := (348277814743/500000000000)
  cov := (294062438327/1000000000000)
  schur := (1041324399163/1000000000000)
  cap := (207935103/200000000000)
  W2 := (3522598554489/1000000000000)
  V := (154475547/500000000000)
  mass := (213473/781250000)
  rootN := (255113259059/250000000000)
  rootB := (1289759987/40000000000)
  rootU := (16055076723/25000000000)
  rootV := (8788502347/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_48.scalar_checked
  centre := fun n hn => lowFull0_48 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy48 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_48.bound (by norm_num) hn lowTIParameters48_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_49 : FrameRectangleCertificate 8000 8250 (969/2000) (97/200) lowTIParameters49 where
  full := (117181438649/1000000000000)
  energy := (348157096253/500000000000)
  cov := (147182622437/500000000000)
  schur := (130189123657/125000000000)
  cap := (65037971/62500000000)
  W2 := (219973990973/62500000000)
  V := (19329327/62500000000)
  mass := (54599413/200000000000)
  rootN := (204109087427/200000000000)
  rootB := (4032306133/125000000000)
  rootU := (16055176339/25000000000)
  rootV := (17586052201/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_49.scalar_checked
  centre := fun n hn => lowFull0_49 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy49 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_49.bound (by norm_num) hn lowTIParameters49_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_50 : FrameRectangleCertificate 8000 8250 (97/200) (971/2000) lowTIParameters50 where
  full := (117283565527/1000000000000)
  energy := (139214573689/200000000000)
  cov := (294668051677/1000000000000)
  schur := (520850842603/500000000000)
  cap := (65096273/62500000000)
  W2 := (3516575711507/1000000000000)
  V := (30958737/100000000000)
  mass := (136384327/500000000000)
  rootN := (1020637881527/1000000000000)
  rootB := (32272904549/1000000000000)
  rootU := (642212221849/1000000000000)
  rootV := (1099693441/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_50.scalar_checked
  centre := fun n hn => lowFull0_50 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy50 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_50.bound (by norm_num) hn lowTIParameters50_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_51 : FrameRectangleCertificate 8000 8250 (971/2000) (243/500) lowTIParameters51 where
  full := (58693042589/500000000000)
  energy := (695831657229/1000000000000)
  cov := (58994171747/200000000000)
  schur := (260472621677/250000000000)
  cap := (41698961/40000000000)
  W2 := (878393525257/250000000000)
  V := (309905509/1000000000000)
  mass := (13627927/50000000000)
  rootN := (4082921477/4000000000)
  rootB := (16143683169/500000000000)
  rootU := (25688743331/40000000000)
  rootV := (8802066647/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_51.scalar_checked
  centre := fun n hn => lowFull0_51 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy51 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_51.bound (by norm_num) hn lowTIParameters51_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_52 : FrameRectangleCertificate 8000 8250 (243/500) (973/2000) lowTIParameters52 where
  full := (117489002269/1000000000000)
  energy := (86948819847/125000000000)
  cov := (5905473321/20000000000)
  schur := (208415878681/200000000000)
  cap := (1043408517/1000000000000)
  W2 := (3510579002837/1000000000000)
  V := (9694489/31250000000)
  mass := (136182599/500000000000)
  rootN := (510411450059/500000000000)
  rootB := (32301834577/1000000000000)
  rootU := (32111307371/50000000000)
  rootV := (17613166893/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_52.scalar_checked
  centre := fun n hn => lowFull0_52 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy52 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_52.bound (by norm_num) hn lowTIParameters52_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_53 : FrameRectangleCertificate 8000 8250 (973/2000) (487/1000) lowTIParameters53 where
  full := (117592321503/1000000000000)
  energy := (69534957301/100000000000)
  cov := (295576473619/1000000000000)
  schur := (130283550621/125000000000)
  cap := (1044343853/1000000000000)
  W2 := (1753795197909/500000000000)
  V := (310541787/1000000000000)
  mass := (136093619/500000000000)
  rootN := (1020915473959/1000000000000)
  rootB := (32316309397/1000000000000)
  rootU := (642234923939/1000000000000)
  rootV := (17622195863/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_53.scalar_checked
  centre := fun n hn => lowFull0_53 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy53 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_53.bound (by norm_num) hn lowTIParameters53_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_54 : FrameRectangleCertificate 8000 8250 (487/1000) (39/80) lowTIParameters54 where
  full := (58848023813/500000000000)
  energy := (43444293741/62500000000)
  cov := (73969820361/250000000000)
  schur := (41698300843/40000000000)
  cap := (1045280047/1000000000000)
  W2 := (1752304129471/500000000000)
  V := (155429963/500000000000)
  mass := (136011693/500000000000)
  rootN := (1021008090603/1000000000000)
  rootB := (6466158201/200000000000)
  rootU := (642244922561/1000000000000)
  rootV := (1101951263/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_54.scalar_checked
  centre := fun n hn => lowFull0_54 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy54 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_54.bound (by norm_num) hn lowTIParameters54_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_55 : FrameRectangleCertificate 8000 8250 (39/80) (61/125) lowTIParameters55 where
  full := (29450046357/250000000000)
  energy := (694867939233/1000000000000)
  cov := (296182089523/1000000000000)
  schur := (521323370687/500000000000)
  cap := (209243421/200000000000)
  W2 := (3501632571191/1000000000000)
  V := (62235613/200000000000)
  mass := (1699203/6250000000)
  rootN := (204220149973/200000000000)
  rootB := (16172639743/500000000000)
  rootU := (321128076547/500000000000)
  rootV := (17640239937/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_55.scalar_checked
  centre := fun n hn => lowFull0_55 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy55 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_55.bound (by norm_num) hn lowTIParameters55_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_56 : FrameRectangleCertificate 8000 8250 (61/125) (977/2000) lowTIParameters56 where
  full := (117904739743/1000000000000)
  energy := (173656822767/250000000000)
  cov := (4632576529/15625000000)
  schur := (20856721311/20000000000)
  cap := (1047155043/1000000000000)
  W2 := (174933165587/50000000000)
  V := (62299241/200000000000)
  mass := (271733457/1000000000000)
  rootN := (1021193451581/1000000000000)
  rootB := (32359775077/1000000000000)
  rootU := (160567156359/250000000000)
  rootV := (4412313771/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_56.scalar_checked
  centre := fun n hn => lowFull0_56 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy56 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_56.bound (by norm_num) hn lowTIParameters56_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_57 : FrameRectangleCertificate 8000 8250 (977/2000) (489/1000) lowTIParameters57 where
  full := (118009715449/1000000000000)
  energy := (8679834441/12500000000)
  cov := (7419692661/25000000000)
  schur := (1043025493259/1000000000000)
  cap := (262023467/250000000000)
  W2 := (349570045979/100000000000)
  V := (62362869/200000000000)
  mass := (271605343/1000000000000)
  rootN := (1021286195569/1000000000000)
  rootB := (32374277877/1000000000000)
  rootU := (642282349559/1000000000000)
  rootV := (17658265629/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_57.scalar_checked
  centre := fun n hn => lowFull0_57 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy57 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_57.bound (by norm_num) hn lowTIParameters57_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_58 : FrameRectangleCertificate 8000 8250 (489/1000) (979/2000) lowTIParameters58 where
  full := (118115117463/1000000000000)
  energy := (694146331799/1000000000000)
  cov := (297090515277/1000000000000)
  schur := (1043215024203/1000000000000)
  cap := (524516797/500000000000)
  W2 := (1746371997357/500000000000)
  V := (156066243/500000000000)
  mass := (16967953/62500000000)
  rootN := (1021378981673/1000000000000)
  rootB := (32388788091/1000000000000)
  rootU := (642297335511/1000000000000)
  rootV := (8833635803/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_58.scalar_checked
  centre := fun n hn => lowFull0_58 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy58 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_58.bound (by norm_num) hn lowTIParameters58_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_59 : FrameRectangleCertificate 8000 8250 (979/2000) (49/100) lowTIParameters59 where
  full := (59110475377/500000000000)
  energy := (346953010271/500000000000)
  cov := (29739332437/100000000000)
  schur := (20868093161/20000000000)
  cap := (104997423/100000000000)
  W2 := (3489793895851/1000000000000)
  V := (156225313/500000000000)
  mass := (135689179/500000000000)
  rootN := (1021471809719/1000000000000)
  rootB := (648066117/20000000000)
  rootU := (642313593429/1000000000000)
  rootV := (17676272967/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_59.scalar_checked
  centre := fun n hn => lowFull0_59 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy59 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_59.bound (by norm_num) hn lowTIParameters59_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_60 : FrameRectangleCertificate 8000 8250 (49/100) (981/2000) lowTIParameters60 where
  full := (59163610163/500000000000)
  energy := (173416455359/250000000000)
  cov := (59020627847/200000000000)
  schur := (517255860517/500000000000)
  cap := (1044946211/1000000000000)
  W2 := (108964066959/31250000000)
  V := (310044487/1000000000000)
  mass := (271277927/1000000000000)
  rootN := (50855474657/50000000000)
  rootB := (1293025111/40000000000)
  rootU := (80291391689/125000000000)
  rootV := (17608080163/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_60.scalar_checked
  centre := fun n hn => lowFull0_60 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy60 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_60.bound (by norm_num) hn lowTIParameters60_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_61 : FrameRectangleCertificate 8000 8250 (981/2000) (491/1000) lowTIParameters61 where
  full := (23686786247/200000000000)
  energy := (346712867201/500000000000)
  cov := (295403303917/1000000000000)
  schur := (1034699898251/1000000000000)
  cap := (522941569/500000000000)
  W2 := (3483912714823/1000000000000)
  V := (310359849/1000000000000)
  mass := (271185271/1000000000000)
  rootN := (1017201994813/1000000000000)
  rootB := (32340116543/1000000000000)
  rootU := (32117498303/50000000000)
  rootV := (17617032923/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_61.scalar_checked
  centre := fun n hn => lowFull0_61 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy61 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_61.bound (by norm_num) hn lowTIParameters61_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_62 : FrameRectangleCertificate 8000 8250 (491/1000) (983/2000) lowTIParameters62 where
  full := (4741643543/40000000000)
  energy := (693185759367/1000000000000)
  cov := (18481466803/62500000000)
  schur := (517444088261/500000000000)
  cap := (1046821011/1000000000000)
  W2 := (3480981591959/1000000000000)
  V := (77668803/250000000000)
  mass := (67774941/250000000000)
  rootN := (63580908609/62500000000)
  rootB := (32354613443/1000000000000)
  rootU := (321185050719/500000000000)
  rootV := (3525196233/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_62.scalar_checked
  centre := fun n hn => lowFull0_62 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy62 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_62.bound (by norm_num) hn lowTIParameters62_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_63 : FrameRectangleCertificate 8000 8250 (983/2000) (123/250) lowTIParameters63 where
  full := (59324348747/500000000000)
  energy := (346472948127/500000000000)
  cov := (296003634029/1000000000000)
  schur := (1035076555517/1000000000000)
  cap := (1047759843/1000000000000)
  W2 := (3478056753803/1000000000000)
  V := (12439623/40000000000)
  mass := (135510417/500000000000)
  rootN := (508693560879/500000000000)
  rootB := (32369118663/1000000000000)
  rootU := (160597887527/250000000000)
  rootV := (8817462433/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_63.scalar_checked
  centre := fun n hn => lowFull0_63 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy63 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_63.bound (by norm_num) hn lowTIParameters63_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_64 : FrameRectangleCertificate 8000 8250 (123/250) (197/400) lowTIParameters64 where
  full := (118756763173/1000000000000)
  energy := (346353072493/500000000000)
  cov := (296303799457/1000000000000)
  schur := (258816258731/250000000000)
  cap := (262174911/250000000000)
  W2 := (1737569090107/500000000000)
  V := (155652969/500000000000)
  mass := (270947953/1000000000000)
  rootN := (101747974669/100000000000)
  rootB := (8095908087/250000000000)
  rootU := (128482864517/200000000000)
  rootV := (17643864033/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_64.scalar_checked
  centre := fun n hn => lowFull0_64 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy64 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_64.bound (by norm_num) hn lowTIParameters64_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_65 : FrameRectangleCertificate 8000 8250 (197/400) (493/1000) lowTIParameters65 where
  full := (2377305817/20000000000)
  energy := (346233252743/500000000000)
  cov := (74150991283/250000000000)
  schur := (129431701803/125000000000)
  cap := (1049640427/1000000000000)
  W2 := (3472225851091/1000000000000)
  V := (311621301/1000000000000)
  mass := (423251/1562500000)
  rootN := (508786206187/500000000000)
  rootB := (16199077343/500000000000)
  rootU := (642438429491/1000000000000)
  rootV := (8826399337/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_65.scalar_checked
  centre := fun n hn => lowFull0_65 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy65 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_65.bound (by norm_num) hn lowTIParameters65_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_66 : FrameRectangleCertificate 8000 8250 (493/1000) (987/2000) lowTIParameters66 where
  full := (118974285801/1000000000000)
  energy := (8652837221/12500000000)
  cov := (59380826211/200000000000)
  schur := (64727643357/62500000000)
  cap := (262645551/250000000000)
  W2 := (3469319746481/1000000000000)
  V := (62387333/200000000000)
  mass := (67704613/250000000000)
  rootN := (127208139831/125000000000)
  rootB := (648253717/20000000000)
  rootU := (642463881517/1000000000000)
  rootV := (17661728823/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_66.scalar_checked
  centre := fun n hn => lowFull0_66 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy66 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_66.bound (by norm_num) hn lowTIParameters66_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_67 : FrameRectangleCertificate 8000 8250 (987/2000) (247/500) lowTIParameters67 where
  full := (59541876677/500000000000)
  energy := (691987561493/1000000000000)
  cov := (148602148611/500000000000)
  schur := (1035831072461/1000000000000)
  cap := (1051524987/1000000000000)
  W2 := (866604961619/250000000000)
  V := (78063007/250000000000)
  mass := (33845123/125000000000)
  rootN := (50887893267/50000000000)
  rootB := (6485445203/200000000000)
  rootU := (321245344721/500000000000)
  rootV := (17670654431/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_67.scalar_checked
  centre := fun n hn => lowFull0_67 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy67 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_67.bound (by norm_num) hn lowTIParameters67_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_68 : FrameRectangleCertificate 8000 8250 (247/500) (989/2000) lowTIParameters68 where
  full := (119193698877/1000000000000)
  energy := (691748256849/1000000000000)
  cov := (148752231819/500000000000)
  schur := (129502493801/125000000000)
  cap := (1052468787/1000000000000)
  W2 := (1731763065647/500000000000)
  V := (312567393/1000000000000)
  mass := (270707863/1000000000000)
  rootN := (1017850652311/1000000000000)
  rootB := (32441775337/1000000000000)
  rootU := (642518864117/1000000000000)
  rootV := (17679575589/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_68.scalar_checked
  centre := fun n hn => lowFull0_68 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy68 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_68.bound (by norm_num) hn lowTIParameters68_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_69 : FrameRectangleCertificate 8000 8250 (989/2000) (99/200) lowTIParameters69 where
  full := (59652063893/500000000000)
  energy := (691509063673/1000000000000)
  cov := (2978046303/10000000000)
  schur := (518104463607/500000000000)
  cap := (1053413619/1000000000000)
  W2 := (3460638581171/1000000000000)
  V := (312882757/1000000000000)
  mass := (270658747/1000000000000)
  rootN := (1017943479381/1000000000000)
  rootB := (8114083509/250000000000)
  rootU := (642548416471/1000000000000)
  rootV := (884424611/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_69.scalar_checked
  centre := fun n hn => lowFull0_69 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy69 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_69.bound (by norm_num) hn lowTIParameters69_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_70 : FrameRectangleCertificate 8000 8250 (99/200) (991/2000) lowTIParameters70 where
  full := (119415045549/1000000000000)
  energy := (691269981889/1000000000000)
  cov := (59620959441/200000000000)
  schur := (518199001281/500000000000)
  cap := (1054359493/1000000000000)
  W2 := (3457757176453/1000000000000)
  V := (156599061/500000000000)
  mass := (135306661/500000000000)
  rootN := (509018173193/500000000000)
  rootB := (8117725563/250000000000)
  rootU := (64257935753/100000000000)
  rootV := (8848702193/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_70.scalar_checked
  centre := fun n hn => lowFull0_70 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy70 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_70.bound (by norm_num) hn lowTIParameters70_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_71 : FrameRectangleCertificate 8000 8250 (991/2000) (62/125) lowTIParameters71 where
  full := (119526457673/1000000000000)
  energy := (345515505711/500000000000)
  cov := (74601241089/250000000000)
  schur := (1036587176181/1000000000000)
  cap := (1055306421/1000000000000)
  W2 := (431860237203/125000000000)
  V := (156756743/500000000000)
  mass := (270571299/1000000000000)
  rootN := (1018129253181/1000000000000)
  rootB := (32485480157/1000000000000)
  rootU := (321305849193/500000000000)
  rootV := (17706312039/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_71.scalar_checked
  centre := fun n hn => lowFull0_71 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy71 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_71.bound (by norm_num) hn lowTIParameters71_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_72 : FrameRectangleCertificate 8000 8250 (62/125) (993/2000) lowTIParameters72 where
  full := (119638369719/1000000000000)
  energy := (345396076099/500000000000)
  cov := (298705131751/1000000000000)
  schur := (518388223873/500000000000)
  cap := (1056254419/1000000000000)
  W2 := (138080509007/40000000000)
  V := (78457213/250000000000)
  mass := (135266207/500000000000)
  rootN := (509111099797/500000000000)
  rootB := (6500013597/200000000000)
  rootU := (642645450221/1000000000000)
  rootV := (17715215269/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_72.scalar_checked
  centre := fun n hn => lowFull0_72 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy72 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_72.bound (by norm_num) hn lowTIParameters72_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_73 : FrameRectangleCertificate 8000 8250 (993/2000) (497/1000) lowTIParameters73 where
  full := (11975078729/100000000000)
  energy := (690553404141/1000000000000)
  cov := (29900529939/100000000000)
  schur := (518482908481/500000000000)
  cap := (211440699/200000000000)
  W2 := (689829927943/200000000000)
  V := (314144217/1000000000000)
  mass := (270496423/1000000000000)
  rootN := (15911174773/15625000000)
  rootB := (6502933169/200000000000)
  rootU := (64268062429/100000000000)
  rootV := (8862056999/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_73.scalar_checked
  centre := fun n hn => lowFull0_73 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy73 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_73.bound (by norm_num) hn lowTIParameters73_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_74 : FrameRectangleCertificate 8000 8250 (497/1000) (199/400) lowTIParameters74 where
  full := (119863716041/1000000000000)
  energy := (690314767177/1000000000000)
  cov := (149652733637/500000000000)
  schur := (518577641769/500000000000)
  cap := (211630733/200000000000)
  W2 := (3446292621937/1000000000000)
  V := (314459583/1000000000000)
  mass := (135231551/500000000000)
  rootN := (50920410533/50000000000)
  rootB := (3252927397/100000000000)
  rootU := (642717231939/1000000000000)
  rootV := (1773300829/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_74.scalar_checked
  centre := fun n hn => lowFull0_74 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy74 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_74.bound (by norm_num) hn lowTIParameters74_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_75 : FrameRectangleCertificate 8000 8250 (199/400) (249/500) lowTIParameters75 where
  full := (119977161669/1000000000000)
  energy := (690076241231/1000000000000)
  cov := (299605635399/1000000000000)
  schur := (518672423579/500000000000)
  cap := (1059104941/1000000000000)
  W2 := (688688330523/200000000000)
  V := (314774949/1000000000000)
  mass := (67608061/250000000000)
  rootN := (1018501274991/1000000000000)
  rootB := (3254389253/100000000000)
  rootU := (642755284579/1000000000000)
  rootV := (17741898123/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_75.scalar_checked
  centre := fun n hn => lowFull0_75 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy75 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_75.bound (by norm_num) hn lowTIParameters75_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_76 : FrameRectangleCertificate 8000 8250 (249/500) (997/2000) lowTIParameters76 where
  full := (15011391241/125000000000)
  energy := (172459456557/250000000000)
  cov := (149952901883/500000000000)
  schur := (207506901507/200000000000)
  cap := (1060057337/1000000000000)
  W2 := (430074589073/125000000000)
  V := (63018063/200000000000)
  mass := (270403661/1000000000000)
  rootN := (254648594579/250000000000)
  rootB := (32558521727/1000000000000)
  rootU := (321397396863/500000000000)
  rootV := (1109423969/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_76.scalar_checked
  centre := fun n hn => lowFull0_76 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy76 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_76.bound (by norm_num) hn lowTIParameters76_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_77 : FrameRectangleCertificate 8000 8250 (997/2000) (499/1000) lowTIParameters77 where
  full := (24041125323/200000000000)
  energy := (344799761047/500000000000)
  cov := (37525746547/125000000000)
  schur := (1037724264371/1000000000000)
  cap := (212202173/200000000000)
  W2 := (859439445699/250000000000)
  V := (315405681/1000000000000)
  mass := (135188589/500000000000)
  rootN := (40747500819/40000000000)
  rootB := (32573161729/1000000000000)
  rootU := (128567154193/200000000000)
  rootV := (443991611/25000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_77.scalar_checked
  centre := fun n hn => lowFull0_77 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy77 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_77.bound (by norm_num) hn lowTIParameters77_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_78 : FrameRectangleCertificate 8000 8250 (499/1000) (999/2000) lowTIParameters78 where
  full := (120320657573/1000000000000)
  energy := (344680664379/500000000000)
  cov := (300506141227/1000000000000)
  schur := (64869632337/62500000000)
  cap := (530982769/500000000000)
  W2 := (858731211077/250000000000)
  V := (39465131/125000000000)
  mass := (135176317/500000000000)
  rootN := (40751228053/40000000000)
  rootB := (16293906361/500000000000)
  rootU := (642878227957/1000000000000)
  rootV := (3553708193/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_78.scalar_checked
  centre := fun n hn => lowFull0_78 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy78 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_78.bound (by norm_num) hn lowTIParameters78_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_79 : FrameRectangleCertificate 8000 8250 (999/2000) (1/2) lowTIParameters79 where
  full := (120436228699/1000000000000)
  energy := (689123246139/1000000000000)
  cov := (3760078879/12500000000)
  schur := (519052033143/500000000000)
  cap := (106292137/100000000000)
  W2 := (686419575627/200000000000)
  V := (63207283/200000000000)
  mass := (135164941/500000000000)
  rootN := (509436960351/500000000000)
  rootB := (32602474907/1000000000000)
  rootU := (10045659007/15625000000)
  rootV := (8888706529/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_79.scalar_checked
  centre := fun n hn => lowFull0_79 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy79 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_79.bound (by norm_num) hn lowTIParameters79_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_80 : FrameRectangleCertificate 8000 8250 (1/2) (1001/2000) lowTIParameters80 where
  full := (24110469187/200000000000)
  energy := (688885274171/1000000000000)
  cov := (298494034001/1000000000000)
  schur := (205858658929/200000000000)
  cap := (1057871213/1000000000000)
  W2 := (3429276865527/1000000000000)
  V := (156803533/500000000000)
  mass := (54061757/200000000000)
  rootN := (1014540928029/1000000000000)
  rootB := (2032808261/62500000000)
  rootU := (160741907067/250000000000)
  rootV := (8854477201/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_80.scalar_checked
  centre := fun n hn => lowFull0_80 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy80 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_80.bound (by norm_num) hn lowTIParameters80_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_81 : FrameRectangleCertificate 8000 8250 (1001/2000) (501/1000) lowTIParameters81 where
  full := (60334507639/500000000000)
  energy := (68864741277/100000000000)
  cov := (37348949007/125000000000)
  schur := (64342611059/62500000000)
  cap := (42352957/40000000000)
  W2 := (171323089381/50000000000)
  V := (313919689/1000000000000)
  mass := (270289219/1000000000000)
  rootN := (1014633814213/1000000000000)
  rootB := (1016861711/31250000000)
  rootU := (25720583813/40000000000)
  rootV := (1107361181/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_81.scalar_checked
  centre := fun n hn => lowFull0_81 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy81 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_81.bound (by norm_num) hn lowTIParameters81_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_82 : FrameRectangleCertificate 8000 8250 (501/1000) (1003/2000) lowTIParameters82 where
  full := (30196560693/250000000000)
  energy := (688409661873/1000000000000)
  cov := (299089150349/1000000000000)
  schur := (64354397091/62500000000)
  cap := (529888919/500000000000)
  W2 := (3423652625919/1000000000000)
  V := (314232313/1000000000000)
  mass := (67567767/250000000000)
  rootN := (507363369159/500000000000)
  rootB := (8138557297/250000000000)
  rootU := (160765772407/250000000000)
  rootV := (8863299513/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_82.scalar_checked
  centre := fun n hn => lowFull0_82 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy82 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_82.bound (by norm_num) hn lowTIParameters82_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_83 : FrameRectangleCertificate 8000 8250 (1003/2000) (251/500) lowTIParameters83 where
  full := (120904034503/1000000000000)
  energy := (3440860107/5000000000)
  cov := (149693354439/500000000000)
  schur := (205971804769/200000000000)
  cap := (265183241/250000000000)
  W2 := (3420849361697/1000000000000)
  V := (157272469/500000000000)
  mass := (135127113/500000000000)
  rootN := (507409850083/500000000000)
  rootB := (32568895653/1000000000000)
  rootU := (643113123219/1000000000000)
  rootV := (17735414797/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_83.scalar_checked
  centre := fun n hn => lowFull0_83 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy83 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_83.bound (by norm_num) hn lowTIParameters83_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_84 : FrameRectangleCertificate 8000 8250 (251/500) (201/400) lowTIParameters84 where
  full := (121022396621/1000000000000)
  energy := (687934491279/1000000000000)
  cov := (59936853529/200000000000)
  schur := (1030047787861/1000000000000)
  cap := (1061689319/1000000000000)
  W2 := (854512994129/250000000000)
  V := (157428781/500000000000)
  mass := (270238593/1000000000000)
  rootN := (507456349813/500000000000)
  rootB := (52133719/1600000000)
  rootU := (321582354139/500000000000)
  rootV := (221802827/12500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_84.scalar_checked
  centre := fun n hn => lowFull0_84 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy84 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_84.bound (by norm_num) hn lowTIParameters84_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_85 : FrameRectangleCertificate 8000 8250 (201/400) (503/1000) lowTIParameters85 where
  full := (121141335317/1000000000000)
  energy := (171924267859/250000000000)
  cov := (299981826647/1000000000000)
  schur := (1030236645207/1000000000000)
  cap := (265661729/250000000000)
  W2 := (1707630225969/500000000000)
  V := (315170187/1000000000000)
  mass := (270224081/1000000000000)
  rootN := (1015005736539/1000000000000)
  rootB := (32598265537/1000000000000)
  rootU := (643217857031/1000000000000)
  rootV := (8876516589/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_85.scalar_checked
  centre := fun n hn => lowFull0_85 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy85 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_85.bound (by norm_num) hn lowTIParameters85_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_86 : FrameRectangleCertificate 8000 8250 (503/1000) (1007/2000) lowTIParameters86 where
  full := (24252171367/200000000000)
  energy := (3437298809/5000000000)
  cov := (75069846471/250000000000)
  schur := (1030425595607/1000000000000)
  cap := (106360577/100000000000)
  W2 := (853118692401/250000000000)
  V := (78870703/250000000000)
  mass := (54042121/200000000000)
  rootN := (1015098810761/1000000000000)
  rootB := (32612969353/1000000000000)
  rootU := (160818145449/250000000000)
  rootV := (17761835829/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_86.scalar_checked
  centre := fun n hn => lowFull0_86 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy86 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_86.bound (by norm_num) hn lowTIParameters86_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_87 : FrameRectangleCertificate 8000 8250 (1007/2000) (63/125) lowTIParameters87 where
  full := (121380967473/1000000000000)
  energy := (137444512459/200000000000)
  cov := (150288472679/500000000000)
  schur := (16103353731/15625000000)
  cap := (532282947/500000000000)
  W2 := (852423727807/250000000000)
  V := (315795437/1000000000000)
  mass := (33774761/125000000000)
  rootN := (1015191922143/1000000000000)
  rootB := (6525537201/200000000000)
  rootU := (321664447489/500000000000)
  rootV := (444265853/25000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_87.scalar_checked
  centre := fun n hn => lowFull0_87 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy87 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_87.bound (by norm_num) hn lowTIParameters87_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_88 : FrameRectangleCertificate 8000 8250 (63/125) (1009/2000) lowTIParameters88 where
  full := (30375418393/250000000000)
  energy := (686985472849/1000000000000)
  cov := (75218626267/250000000000)
  schur := (128850471807/125000000000)
  cap := (532763651/500000000000)
  W2 := (17034604293/5000000000)
  V := (158054031/500000000000)
  mass := (270186459/1000000000000)
  rootN := (507642535269/500000000000)
  rootB := (32642415689/1000000000000)
  rootU := (643386809041/1000000000000)
  rootV := (17779428057/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_88.scalar_checked
  centre := fun n hn => lowFull0_88 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy88 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_88.bound (by norm_num) hn lowTIParameters88_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_89 : FrameRectangleCertificate 8000 8250 (1009/2000) (101/200) lowTIParameters89 where
  full := (30405745383/250000000000)
  energy := (686748493389/1000000000000)
  cov := (301172065009/1000000000000)
  schur := (20619860047/20000000000)
  cap := (1066490011/1000000000000)
  W2 := (3404152593647/1000000000000)
  V := (19776293/62500000000)
  mass := (135087827/500000000000)
  rootN := (5076891279/5000000000)
  rootB := (32657158649/1000000000000)
  rootU := (321723168279/500000000000)
  rootV := (8894108837/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_89.scalar_checked
  centre := fun n hn => lowFull0_89 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy89 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_89.bound (by norm_num) hn lowTIParameters89_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_90 : FrameRectangleCertificate 8000 8250 (101/200) (1011/2000) lowTIParameters90 where
  full := (121744897801/1000000000000)
  energy := (343255811921/500000000000)
  cov := (75367406297/250000000000)
  schur := (257795580549/250000000000)
  cap := (66715877/62500000000)
  W2 := (340139009827/100000000000)
  V := (158366657/500000000000)
  mass := (27016561/100000000000)
  rootN := (507735738893/500000000000)
  rootB := (6534383007/200000000000)
  rootU := (643507490163/1000000000000)
  rootV := (355940059/20000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_90.scalar_checked
  centre := fun n hn => lowFull0_90 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy90 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_90.bound (by norm_num) hn lowTIParameters90_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_91 : FrameRectangleCertificate 8000 8250 (1011/2000) (253/500) lowTIParameters91 where
  full := (30466857221/250000000000)
  energy := (137254972827/200000000000)
  cov := (150883592799/500000000000)
  schur := (1031371733697/1000000000000)
  cap := (534209691/500000000000)
  W2 := (424829169313/125000000000)
  V := (15852297/50000000000)
  mass := (270156273/1000000000000)
  rootN := (50778236817/50000000000)
  rootB := (1021458909/31250000000)
  rootU := (64357028259/100000000000)
  rootV := (4451445973/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_91.scalar_checked
  centre := fun n hn => lowFull0_91 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy91 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_91.bound (by norm_num) hn lowTIParameters91_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_92 : FrameRectangleCertificate 8000 8250 (253/500) (1013/2000) lowTIParameters92 where
  full := (121990581331/1000000000000)
  energy := (343019107099/500000000000)
  cov := (235988083/781250000)
  schur := (206312247323/200000000000)
  cap := (42775443/40000000000)
  W2 := (1697941172259/500000000000)
  V := (317358567/1000000000000)
  mass := (27014759/100000000000)
  rootN := (203131606267/200000000000)
  rootB := (8175367251/250000000000)
  rootU := (321817363321/500000000000)
  rootV := (8907280267/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_92.scalar_checked
  centre := fun n hn => lowFull0_92 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy92 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_92.bound (by norm_num) hn lowTIParameters92_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_93 : FrameRectangleCertificate 8000 8250 (1013/2000) (507/1000) lowTIParameters93 where
  full := (122114361747/1000000000000)
  energy := (685801673953/1000000000000)
  cov := (151181153559/500000000000)
  schur := (515875415329/500000000000)
  cap := (8562833/8000000000)
  W2 := (3393137050379/1000000000000)
  V := (317671193/1000000000000)
  mass := (135069757/500000000000)
  rootN := (1015751362617/1000000000000)
  rootB := (32716266979/1000000000000)
  rootU := (643700835193/1000000000000)
  rootV := (8911666413/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_93.scalar_checked
  centre := fun n hn => lowFull0_93 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy93 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_93.bound (by norm_num) hn lowTIParameters93_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_94 : FrameRectangleCertificate 8000 8250 (507/1000) (203/400) lowTIParameters94 where
  full := (30559694197/250000000000)
  energy := (171391310833/250000000000)
  cov := (151329934113/500000000000)
  schur := (515970257779/500000000000)
  cap := (21426471/20000000000)
  W2 := (84759936361/25000000000)
  V := (15899191/50000000000)
  mass := (270132001/1000000000000)
  rootN := (253961182511/250000000000)
  rootB := (8182769817/250000000000)
  rootU := (643768621211/1000000000000)
  rootV := (1783210083/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_94.scalar_checked
  centre := fun n hn => lowFull0_94 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy94 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_94.bound (by norm_num) hn lowTIParameters94_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_95 : FrameRectangleCertificate 8000 8250 (203/400) (127/250) lowTIParameters95 where
  full := (61181916583/500000000000)
  energy := (685328922263/1000000000000)
  cov := (151478714783/500000000000)
  schur := (1032130291057/1000000000000)
  cap := (536147181/500000000000)
  W2 := (211728971187/62500000000)
  V := (318296447/1000000000000)
  mass := (270125009/1000000000000)
  rootN := (25398453337/25000000000)
  rootB := (6549181207/200000000000)
  rootU := (128767619549/200000000000)
  rootV := (8920432263/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_95.scalar_checked
  centre := fun n hn => lowFull0_95 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy95 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_95.bound (by norm_num) hn lowTIParameters95_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_96 : FrameRectangleCertificate 8000 8250 (127/250) (1017/2000) lowTIParameters96 where
  full := (7655596103/62500000000)
  energy := (685092710671/1000000000000)
  cov := (303254991137/1000000000000)
  schur := (1651712251/1600000000)
  cap := (1073266577/1000000000000)
  W2 := (3384935286419/1000000000000)
  V := (12744363/40000000000)
  mass := (135059251/500000000000)
  rootN := (40641262911/40000000000)
  rootB := (2047546719/62500000000)
  rootU := (643909277929/1000000000000)
  rootV := (8924811973/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_96.scalar_checked
  centre := fun n hn => lowFull0_96 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy96 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_96.bound (by norm_num) hn lowTIParameters96_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_97 : FrameRectangleCertificate 8000 8250 (1017/2000) (509/1000) lowTIParameters97 where
  full := (30653974261/250000000000)
  energy := (342428304243/500000000000)
  cov := (15177627647/50000000000)
  schur := (1032510112749/1000000000000)
  cap := (1074240211/1000000000000)
  W2 := (676442535839/200000000000)
  V := (159460851/500000000000)
  mass := (67528111/250000000000)
  rootN := (63507815487/62500000000)
  rootB := (327756039/10000000000)
  rootU := (12879643499/20000000000)
  rootV := (8929189521/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_97.scalar_checked
  centre := fun n hn => lowFull0_97 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy97 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_97.bound (by norm_num) hn lowTIParameters97_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_98 : FrameRectangleCertificate 8000 8250 (509/1000) (1019/2000) lowTIParameters98 where
  full := (61371459117/500000000000)
  energy := (171155153909/250000000000)
  cov := (75962528743/250000000000)
  schur := (1032700158419/1000000000000)
  cap := (13440191/12500000000)
  W2 := (675899139981/200000000000)
  V := (31923433/100000000000)
  mass := (270106803/1000000000000)
  rootN := (127027319799/125000000000)
  rootB := (32790475447/1000000000000)
  rootU := (644056802127/1000000000000)
  rootV := (4466782469/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_98.scalar_checked
  centre := fun n hn => lowFull0_98 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy98 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_98.bound (by norm_num) hn lowTIParameters98_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_99 : FrameRectangleCertificate 8000 8250 (1019/2000) (51/100) lowTIParameters99 where
  full := (122870608133/1000000000000)
  energy := (42774045753/62500000000)
  cov := (76036919309/250000000000)
  schur := (103289029363/100000000000)
  cap := (1076191797/1000000000000)
  W2 := (67535686623/20000000000)
  V := (159773479/500000000000)
  mass := (5402031/20000000000)
  rootN := (25407802611/25000000000)
  rootB := (32805362321/1000000000000)
  rootU := (644133172801/1000000000000)
  rootV := (17875876427/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_99.scalar_checked
  centre := fun n hn => lowFull0_99 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy99 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_99.bound (by norm_num) hn lowTIParameters99_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_100 : FrameRectangleCertificate 8000 8250 (51/100) (1021/2000) lowTIParameters100 where
  full := (122998973721/1000000000000)
  energy := (684148957649/1000000000000)
  cov := (150906806129/500000000000)
  schur := (512079229343/500000000000)
  cap := (133890731/125000000000)
  W2 := (3374078555559/1000000000000)
  V := (317094717/1000000000000)
  mass := (54019331/200000000000)
  rootN := (202401428719/200000000000)
  rootB := (4091007379/125000000000)
  rootU := (32210565021/50000000000)
  rootV := (3561430707/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_100.scalar_checked
  centre := fun n hn => lowFull0_100 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy100 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_100.bound (by norm_num) hn lowTIParameters100_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_101 : FrameRectangleCertificate 8000 8250 (1021/2000) (511/1000) lowTIParameters101 where
  full := (30782005509/250000000000)
  energy := (683913292373/1000000000000)
  cov := (302108595807/1000000000000)
  schur := (128043389929/125000000000)
  cap := (134012491/125000000000)
  W2 := (3371378356009/1000000000000)
  V := (79351159/250000000000)
  mass := (54018419/200000000000)
  rootN := (253025087619/250000000000)
  rootB := (32742937071/1000000000000)
  rootU := (80536399817/125000000000)
  rootV := (8907926751/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_101.scalar_checked
  centre := fun n hn => lowFull0_101 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy101 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_101.bound (by norm_num) hn lowTIParameters101_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_102 : FrameRectangleCertificate 8000 8250 (511/1000) (1023/2000) lowTIParameters102 where
  full := (123257760159/1000000000000)
  energy := (683677736143/1000000000000)
  cov := (151201789793/500000000000)
  schur := (1024535868173/1000000000000)
  cap := (67067219/62500000000)
  W2 := (3368683715273/1000000000000)
  V := (63542911/200000000000)
  mass := (54017569/200000000000)
  rootN := (1012193592241/1000000000000)
  rootB := (16378915593/500000000000)
  rootU := (644372880737/1000000000000)
  rootV := (17824549223/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_102.scalar_checked
  centre := fun n hn => lowFull0_102 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy102 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_102.bound (by norm_num) hn lowTIParameters102_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_103 : FrameRectangleCertificate 8000 8250 (1023/2000) (64/125) lowTIParameters103 where
  full := (123388195233/1000000000000)
  energy := (683442288889/1000000000000)
  cov := (302698563591/1000000000000)
  schur := (8197797637/8000000000)
  cap := (537026297/500000000000)
  W2 := (3365994616231/1000000000000)
  V := (12720979/40000000000)
  mass := (270083883/1000000000000)
  rootN := (1012286868741/1000000000000)
  rootB := (32772741631/1000000000000)
  rootU := (644456360711/1000000000000)
  rootV := (4458310183/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_103.scalar_checked
  centre := fun n hn => lowFull0_103 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy103 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_103.bound (by norm_num) hn lowTIParameters103_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_104 : FrameRectangleCertificate 8000 8250 (64/125) (41/80) lowTIParameters104 where
  full := (15439916807/125000000000)
  energy := (683206950541/1000000000000)
  cov := (151496773909/500000000000)
  schur := (512456814267/500000000000)
  cap := (1075031217/1000000000000)
  W2 := (3363311041893/1000000000000)
  V := (159167197/500000000000)
  mass := (270080189/1000000000000)
  rootN := (1012380179841/1000000000000)
  rootB := (32787668673/1000000000000)
  rootU := (644541652233/1000000000000)
  rootV := (17841927979/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_104.scalar_checked
  centre := fun n hn => lowFull0_104 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy104 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_104.bound (by norm_num) hn lowTIParameters104_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_105 : FrameRectangleCertificate 8000 8250 (41/80) (513/1000) lowTIParameters105 where
  full := (3091279627/25000000000)
  energy := (341485860513/500000000000)
  cov := (303288532271/1000000000000)
  schur := (256275659913/250000000000)
  cap := (215202277/200000000000)
  W2 := (3360632975279/1000000000000)
  V := (159322157/500000000000)
  mass := (33759593/125000000000)
  rootN := (31639797669/31250000000)
  rootB := (32802612473/1000000000000)
  rootU := (161157192287/250000000000)
  rootV := (8925305513/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_105.scalar_checked
  centre := fun n hn => lowFull0_105 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy105 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_105.bound (by norm_num) hn lowTIParameters105_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_106 : FrameRectangleCertificate 8000 8250 (513/1000) (1027/2000) lowTIParameters106 where
  full := (123783754407/1000000000000)
  energy := (27309464011/40000000000)
  cov := (303583516949/1000000000000)
  schur := (64080733609/62500000000)
  cap := (538496559/500000000000)
  W2 := (671592079911/200000000000)
  V := (159477117/500000000000)
  mass := (27007353/100000000000)
  rootN := (506283452659/500000000000)
  rootB := (32817573311/1000000000000)
  rootU := (644717725371/1000000000000)
  rootV := (4464822463/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_106.scalar_checked
  centre := fun n hn => lowFull0_106 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy106 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_106.bound (by norm_num) hn lowTIParameters106_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_107 : FrameRectangleCertificate 8000 8250 (1027/2000) (257/500) lowTIParameters107 where
  full := (61958524903/500000000000)
  energy := (136500317643/200000000000)
  cov := (303878501851/1000000000000)
  schur := (1025480922533/1000000000000)
  cap := (1077976431/1000000000000)
  W2 := (3355293297841/1000000000000)
  V := (159632077/500000000000)
  mass := (67517633/250000000000)
  rootN := (1012660319423/1000000000000)
  rootB := (16416275697/500000000000)
  rootU := (322404267459/500000000000)
  rootV := (8933982231/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_107.scalar_checked
  centre := fun n hn => lowFull0_107 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy107 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_107.bound (by norm_num) hn lowTIParameters107_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_108 : FrameRectangleCertificate 8000 8250 (257/500) (1029/2000) lowTIParameters108 where
  full := (12405107869/100000000000)
  energy := (85283335597/125000000000)
  cov := (304173486979/1000000000000)
  schur := (205134038759/200000000000)
  cap := (539480671/500000000000)
  W2 := (3352631653439/1000000000000)
  V := (12782963/40000000000)
  mass := (135033867/500000000000)
  rootN := (253188441901/250000000000)
  rootB := (32847546971/1000000000000)
  rootU := (644901211861/1000000000000)
  rootV := (17876634891/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_108.scalar_checked
  centre := fun n hn => lowFull0_108 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy108 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_108.bound (by norm_num) hn lowTIParameters108_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_109 : FrameRectangleCertificate 8000 8250 (1029/2000) (103/200) lowTIParameters109 where
  full := (62092924269/500000000000)
  energy := (682031889889/1000000000000)
  cov := (38058559041/125000000000)
  schur := (1025859551257/1000000000000)
  cap := (215989573/200000000000)
  W2 := (1674987724831/500000000000)
  V := (63976799/200000000000)
  mass := (270065123/1000000000000)
  rootN := (253211812429/250000000000)
  rootB := (4107820029/125000000000)
  rootU := (161248942593/250000000000)
  rootV := (558915659/31250000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_109.scalar_checked
  centre := fun n hn => lowFull0_109 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy109 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_109.bound (by norm_num) hn lowTIParameters109_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_110 : FrameRectangleCertificate 8000 8250 (103/200) (1031/2000) lowTIParameters110 where
  full := (31080341719/250000000000)
  energy := (681797203479/1000000000000)
  cov := (304763457901/1000000000000)
  schur := (1026048994679/1000000000000)
  cap := (1080936019/1000000000000)
  W2 := (104603895933/31250000000)
  V := (80048479/250000000000)
  mass := (54012537/200000000000)
  rootN := (15827199463/15625000000)
  rootB := (16438795721/500000000000)
  rootU := (322546112337/500000000000)
  rootV := (17893963117/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_110.scalar_checked
  centre := fun n hn => lowFull0_110 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy110 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_110.bound (by norm_num) hn lowTIParameters110_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_111 : FrameRectangleCertificate 8000 8250 (1031/2000) (129/250) lowTIParameters111 where
  full := (7778602581/62500000000)
  energy := (340781312741/500000000000)
  cov := (152529221847/500000000000)
  schur := (64139907739/62500000000)
  cap := (1081925821/1000000000000)
  W2 := (3344679297579/1000000000000)
  V := (160251919/500000000000)
  mass := (270060409/1000000000000)
  rootN := (506517157613/500000000000)
  rootB := (16446320417/500000000000)
  rootU := (40324411819/62500000000)
  rootV := (8951310491/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_111.scalar_checked
  centre := fun n hn => lowFull0_111 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy111 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_111.bound (by norm_num) hn lowTIParameters111_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_112 : FrameRectangleCertificate 8000 8250 (129/250) (1033/2000) lowTIParameters112 where
  full := (31148669861/250000000000)
  energy := (340664077911/500000000000)
  cov := (305353429711/1000000000000)
  schur := (256607034607/250000000000)
  cap := (1082917287/1000000000000)
  W2 := (3342039316253/1000000000000)
  V := (320813759/1000000000000)
  mass := (135029141/500000000000)
  rootN := (1013127898357/1000000000000)
  rootB := (16453854313/500000000000)
  rootU := (645290878053/1000000000000)
  rootV := (8955637317/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_112.scalar_checked
  centre := fun n hn => lowFull0_112 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy112 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_112.bound (by norm_num) hn lowTIParameters112_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_113 : FrameRectangleCertificate 8000 8250 (1033/2000) (517/1000) lowTIParameters113 where
  full := (31183122253/250000000000)
  energy := (681093794431/1000000000000)
  cov := (305648415949/1000000000000)
  schur := (1026617838261/1000000000000)
  cap := (1083910437/1000000000000)
  W2 := (667880941907/200000000000)
  V := (321123681/1000000000000)
  mass := (33757037/125000000000)
  rootN := (1013221514903/1000000000000)
  rootB := (16461397549/500000000000)
  rootU := (322696552987/500000000000)
  rootV := (3583984827/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_113.scalar_checked
  centre := fun n hn => lowFull0_113 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy113 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_113.bound (by norm_num) hn lowTIParameters113_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_114 : FrameRectangleCertificate 8000 8250 (517/1000) (207/400) lowTIParameters114 where
  full := (12487107777/100000000000)
  energy := (340429770619/500000000000)
  cov := (305943402407/1000000000000)
  schur := (1026807623071/1000000000000)
  cap := (216981057/200000000000)
  W2 := (3336775461073/1000000000000)
  V := (321433603/1000000000000)
  mass := (270054441/1000000000000)
  rootN := (101331516473/100000000000)
  rootB := (16468950217/500000000000)
  rootU := (645497287447/1000000000000)
  rootV := (2241071183/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_114.scalar_checked
  centre := fun n hn => lowFull0_114 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy114 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_114.bound (by norm_num) hn lowTIParameters114_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_115 : FrameRectangleCertificate 8000 8250 (207/400) (259/500) lowTIParameters115 where
  full := (31252613381/250000000000)
  energy := (680625396173/1000000000000)
  cov := (153119194543/500000000000)
  schur := (205399498523/200000000000)
  cap := (21718037/20000000000)
  W2 := (1667075777281/500000000000)
  V := (12869741/40000000000)
  mass := (270052707/1000000000000)
  rootN := (101340884771/100000000000)
  rootB := (329530249/10000000000)
  rootU := (161400859267/250000000000)
  rootV := (28699537/1600000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_115.scalar_checked
  centre := fun n hn => lowFull0_115 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy115 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_115.bound (by norm_num) hn lowTIParameters115_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_116 : FrameRectangleCertificate 8000 8250 (259/500) (1037/2000) lowTIParameters116 where
  full := (125150624153/1000000000000)
  energy := (680391359169/1000000000000)
  cov := (19158335999/62500000000)
  schur := (1027187446667/1000000000000)
  cap := (1086900149/1000000000000)
  W2 := (3331532973873/1000000000000)
  V := (322053447/1000000000000)
  mass := (135025543/500000000000)
  rootN := (25337564093/25000000000)
  rootB := (8242042181/250000000000)
  rootU := (645711569563/1000000000000)
  rootV := (8972923813/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_116.scalar_checked
  centre := fun n hn => lowFull0_116 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy116 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_116.bound (by norm_num) hn lowTIParameters116_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_117 : FrameRectangleCertificate 8000 8250 (1037/2000) (519/1000) lowTIParameters117 where
  full := (31322899397/250000000000)
  energy := (13603148603/20000000000)
  cov := (306828363103/1000000000000)
  schur := (1027377484967/1000000000000)
  cap := (543950101/500000000000)
  W2 := (83222992569/25000000000)
  V := (32236337/100000000000)
  mass := (27004957/100000000000)
  rootN := (506798156313/500000000000)
  rootB := (6596666437/200000000000)
  rootU := (645821699699/1000000000000)
  rootV := (35908961/2000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_117.scalar_checked
  centre := fun n hn => lowFull0_117 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy117 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_117.bound (by norm_num) hn lowTIParameters117_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_118 : FrameRectangleCertificate 8000 8250 (519/1000) (1039/2000) lowTIParameters118 where
  full := (25086676363/200000000000)
  energy := (169980902263/250000000000)
  cov := (307123350439/1000000000000)
  schur := (1027567607283/1000000000000)
  cap := (43556081/40000000000)
  W2 := (1663155862621/500000000000)
  V := (322673293/1000000000000)
  mass := (270048153/1000000000000)
  rootN := (1013690094301/1000000000000)
  rootB := (32998515497/1000000000000)
  rootU := (645933842331/1000000000000)
  rootV := (718524369/40000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_118.scalar_checked
  centre := fun n hn => lowFull0_118 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy118 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_118.bound (by norm_num) hn lowTIParameters118_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_119 : FrameRectangleCertificate 8000 8250 (1039/2000) (13/25) lowTIParameters119 where
  full := (125575984893/1000000000000)
  energy := (135937979161/200000000000)
  cov := (61483667599/200000000000)
  schur := (102775781339/100000000000)
  cap := (272476409/250000000000)
  W2 := (3323709025293/1000000000000)
  V := (20186451/62500000000)
  mass := (67511707/250000000000)
  rootN := (1013783908627/1000000000000)
  rootB := (16506859453/500000000000)
  rootU := (323024006209/500000000000)
  rootV := (17971733807/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_119.scalar_checked
  centre := fun n hn => lowFull0_119 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy119 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_119.bound (by norm_num) hn lowTIParameters119_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_120 : FrameRectangleCertificate 8000 8250 (13/25) (1041/2000) lowTIParameters120 where
  full := (25143882983/200000000000)
  energy := (135891258067/200000000000)
  cov := (152531388061/500000000000)
  schur := (509550933831/500000000000)
  cap := (1084831199/1000000000000)
  W2 := (830277896733/250000000000)
  V := (320508389/1000000000000)
  mass := (67511397/250000000000)
  rootN := (1009505754151/1000000000000)
  rootB := (4117096973/125000000000)
  rootU := (20192632029/31250000000)
  rootV := (8951374043/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_120.scalar_checked
  centre := fun n hn => lowFull0_120 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy120 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_120.bound (by norm_num) hn lowTIParameters120_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_121 : FrameRectangleCertificate 8000 8250 (1041/2000) (521/1000) lowTIParameters121 where
  full := (125863680049/1000000000000)
  energy := (5306428067/7812500000)
  cov := (305355216301/1000000000000)
  schur := (63705662079/62500000000)
  cap := (217166629/200000000000)
  W2 := (3318519394299/1000000000000)
  V := (80203909/250000000000)
  mass := (270044429/1000000000000)
  rootN := (1009599224081/1000000000000)
  rootB := (16475991207/500000000000)
  rootU := (80785311869/125000000000)
  rootV := (17911327031/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_121.scalar_checked
  centre := fun n hn => lowFull0_121 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy121 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_121.bound (by norm_num) hn lowTIParameters121_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_122 : FrameRectangleCertificate 8000 8250 (521/1000) (1043/2000) lowTIParameters122 where
  full := (126008788529/1000000000000)
  energy := (339494701229/500000000000)
  cov := (305647656693/1000000000000)
  schur := (254869850303/250000000000)
  cap := (135854617/125000000000)
  W2 := (3315932431577/1000000000000)
  V := (321122883/1000000000000)
  mass := (270043343/1000000000000)
  rootN := (1009692726137/1000000000000)
  rootB := (32967210013/1000000000000)
  rootU := (64640283767/100000000000)
  rootV := (1791990187/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_122.scalar_checked
  centre := fun n hn => lowFull0_122 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy122 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_122.bound (by norm_num) hn lowTIParameters122_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_123 : FrameRectangleCertificate 8000 8250 (1043/2000) (261/500) lowTIParameters123 where
  full := (1009237989/8000000000)
  energy := (84844514989/125000000000)
  cov := (305940097303/1000000000000)
  schur := (10196682913/10000000000)
  cap := (1087842593/1000000000000)
  W2 := (1656675341507/500000000000)
  V := (32143013/100000000000)
  mass := (270042327/1000000000000)
  rootN := (504893130103/500000000000)
  rootB := (32982458869/1000000000000)
  rootU := (646525268279/1000000000000)
  rootV := (17928472607/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_123.scalar_checked
  centre := fun n hn => lowFull0_123 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy123 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_123.bound (by norm_num) hn lowTIParameters123_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_124 : FrameRectangleCertificate 8000 8250 (261/500) (209/400) lowTIParameters124 where
  full := (25260313739/200000000000)
  energy := (678522944871/1000000000000)
  cov := (489972061/1600000000)
  schur := (1019857263283/1000000000000)
  cap := (1088850129/1000000000000)
  W2 := (3310774132973/1000000000000)
  V := (160868689/500000000000)
  mass := (8438793/31250000000)
  rootN := (12623497827/12500000000)
  rootB := (659954583/20000000000)
  rootU := (323324901063/500000000000)
  rootV := (17937039277/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_124.scalar_checked
  centre := fun n hn => lowFull0_124 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy124 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_124.bound (by norm_num) hn lowTIParameters124_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_125 : FrameRectangleCertificate 8000 8250 (209/400) (523/1000) lowTIParameters125 where
  full := (12644925713/100000000000)
  energy := (33914493863/50000000000)
  cov := (306524979159/1000000000000)
  schur := (1020046316913/1000000000000)
  cap := (68116223/62500000000)
  W2 := (1654101382869/500000000000)
  V := (2576357/8000000000)
  mass := (54008097/200000000000)
  rootN := (201994684773/200000000000)
  rootB := (33013021189/1000000000000)
  rootU := (646776454553/1000000000000)
  rootV := (17945601829/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_125.scalar_checked
  centre := fun n hn => lowFull0_125 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy125 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_125.bound (by norm_num) hn lowTIParameters125_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_126 : FrameRectangleCertificate 8000 8250 (523/1000) (1047/2000) lowTIParameters126 where
  full := (63298911199/500000000000)
  energy := (84757114627/125000000000)
  cov := (306817420409/1000000000000)
  schur := (204047090399/200000000000)
  cap := (68179433/62500000000)
  W2 := (1652818282907/500000000000)
  V := (322351873/1000000000000)
  mass := (270039651/1000000000000)
  rootN := (505033526609/500000000000)
  rootB := (3302833523/100000000000)
  rootU := (64690524103/100000000000)
  rootV := (8977080163/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_126.scalar_checked
  centre := fun n hn => lowFull0_126 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy126 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_126.bound (by norm_num) hn lowTIParameters126_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_127 : FrameRectangleCertificate 8000 8250 (1047/2000) (131/250) lowTIParameters127 where
  full := (63373636511/500000000000)
  energy := (169456016017/250000000000)
  cov := (30710986187/100000000000)
  schur := (510212334137/500000000000)
  cap := (43675369/40000000000)
  W2 := (3303075517681/1000000000000)
  V := (322659121/1000000000000)
  mass := (27003887/100000000000)
  rootN := (505080357041/500000000000)
  rootB := (16521835741/500000000000)
  rootU := (323518088541/500000000000)
  rootV := (3592542949/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_127.scalar_checked
  centre := fun n hn => lowFull0_127 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy127 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_127.bound (by norm_num) hn lowTIParameters127_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_128 : FrameRectangleCertificate 8000 8250 (131/250) (1049/2000) lowTIParameters128 where
  full := (126897617583/1000000000000)
  energy := (338795659173/500000000000)
  cov := (61480460709/200000000000)
  schur := (1020613965541/1000000000000)
  cap := (1092899481/1000000000000)
  W2 := (1650259802949/500000000000)
  V := (322966369/1000000000000)
  mass := (135019069/500000000000)
  rootN := (505127203173/500000000000)
  rootB := (33059030249/1000000000000)
  rootU := (6471692783/10000000000)
  rootV := (4492816273/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_128.scalar_checked
  centre := fun n hn => lowFull0_128 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy128 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_128.bound (by norm_num) hn lowTIParameters128_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_129 : FrameRectangleCertificate 8000 8250 (1049/2000) (21/40) lowTIParameters129 where
  full := (1588110809/12500000000)
  energy := (338679339891/500000000000)
  cov := (38461843179/125000000000)
  schur := (1020803343561/1000000000000)
  cap := (218783343/200000000000)
  W2 := (1648984407541/500000000000)
  V := (161636809/500000000000)
  mass := (67509363/250000000000)
  rootN := (202069625977/200000000000)
  rootB := (33074411787/1000000000000)
  rootU := (647304560341/1000000000000)
  rootV := (17979811401/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_129.scalar_checked
  centre := fun n hn => lowFull0_129 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy129 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_129.bound (by norm_num) hn lowTIParameters129_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_130 : FrameRectangleCertificate 8000 8250 (21/40) (1051/2000) lowTIParameters130 where
  full := (127201023151/1000000000000)
  energy := (677126148311/1000000000000)
  cov := (307987187529/1000000000000)
  schur := (510496401063/500000000000)
  cap := (547467973/500000000000)
  W2 := (329542312999/100000000000)
  V := (323580867/1000000000000)
  mass := (270036809/1000000000000)
  rootN := (1010441884587/1000000000000)
  rootB := (33089816349/1000000000000)
  rootU := (647442038989/1000000000000)
  rootV := (17988353649/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_130.scalar_checked
  centre := fun n hn => lowFull0_130 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy130 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_130.bound (by norm_num) hn lowTIParameters130_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_131 : FrameRectangleCertificate 8000 8250 (1051/2000) (263/500) lowTIParameters131 where
  full := (31838525407/250000000000)
  energy := (676893723859/1000000000000)
  cov := (308279629837/1000000000000)
  schur := (1021182340983/1000000000000)
  cap := (219191439/200000000000)
  W2 := (3292882535269/1000000000000)
  V := (64777623/200000000000)
  mass := (270036207/1000000000000)
  rootN := (1010535670317/1000000000000)
  rootB := (33105244223/1000000000000)
  rootU := (647581730013/1000000000000)
  rootV := (3599378363/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_131.scalar_checked
  centre := fun n hn => lowFull0_131 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy131 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_131.bound (by norm_num) hn lowTIParameters131_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_132 : FrameRectangleCertificate 8000 8250 (263/500) (1053/2000) lowTIParameters132 where
  full := (31877027247/250000000000)
  energy := (676661406363/1000000000000)
  cov := (308572072357/1000000000000)
  schur := (1021371959949/1000000000000)
  cap := (1096980479/1000000000000)
  W2 := (3290347015831/1000000000000)
  V := (64839073/200000000000)
  mass := (135017821/500000000000)
  rootN := (505314743489/500000000000)
  rootB := (3312069563/100000000000)
  rootU := (161930912333/250000000000)
  rootV := (4501356497/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_132.scalar_checked
  centre := fun n hn => lowFull0_132 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy132 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_132.bound (by norm_num) hn lowTIParameters132_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_133 : FrameRectangleCertificate 8000 8250 (1053/2000) (527/1000) lowTIParameters133 where
  full := (12766305411/100000000000)
  energy := (84553649469/125000000000)
  cov := (61772903017/200000000000)
  schur := (63847603673/62500000000)
  cap := (1098005819/1000000000000)
  W2 := (3287816556467/1000000000000)
  V := (162251307/500000000000)
  mass := (33754389/125000000000)
  rootN := (505361667217/500000000000)
  rootB := (33136170857/1000000000000)
  rootU := (64786781287/100000000000)
  rootV := (1801395609/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_133.scalar_checked
  centre := fun n hn => lowFull0_133 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy133 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_133.bound (by norm_num) hn lowTIParameters133_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_134 : FrameRectangleCertificate 8000 8250 (527/1000) (211/400) lowTIParameters134 where
  full := (127818945947/1000000000000)
  energy := (16904927299/25000000000)
  cov := (38644619753/125000000000)
  schur := (510875718627/500000000000)
  cap := (1099033237/1000000000000)
  W2 := (3285291142187/1000000000000)
  V := (40601233/125000000000)
  mass := (54006923/200000000000)
  rootN := (1010817212583/1000000000000)
  rootB := (165758351/5000000000)
  rootU := (162003559167/250000000000)
  rootV := (9011241091/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_134.scalar_checked
  centre := fun n hn => lowFull0_134 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy134 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_134.bound (by norm_num) hn lowTIParameters134_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_135 : FrameRectangleCertificate 8000 8250 (211/400) (66/125) lowTIParameters135 where
  full := (25595158703/200000000000)
  energy := (135193018983/200000000000)
  cov := (77362350293/250000000000)
  schur := (255485323789/250000000000)
  cap := (1100062751/1000000000000)
  W2 := (32827707579/10000000000)
  V := (325117113/1000000000000)
  mass := (270034149/1000000000000)
  rootN := (202182224259/200000000000)
  rootB := (33167193897/1000000000000)
  rootU := (648162936823/1000000000000)
  rootV := (3606200843/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_135.scalar_checked
  centre := fun n hn => lowFull0_135 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy135 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_135.bound (by norm_num) hn lowTIParameters135_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_136 : FrameRectangleCertificate 8000 8250 (66/125) (1057/2000) lowTIParameters136 where
  full := (128133605881/1000000000000)
  energy := (84466650569/125000000000)
  cov := (309741844529/1000000000000)
  schur := (255532808067/250000000000)
  cap := (1101094381/1000000000000)
  W2 := (32802553887/10000000000)
  V := (325424363/1000000000000)
  mass := (270033711/1000000000000)
  rootN := (1011005060457/1000000000000)
  rootB := (33182742217/1000000000000)
  rootU := (324156964743/500000000000)
  rootV := (72158089/4000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_136.scalar_checked
  centre := fun n hn => lowFull0_136 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy136 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_136.bound (by norm_num) hn lowTIParameters136_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_137 : FrameRectangleCertificate 8000 8250 (1057/2000) (529/1000) lowTIParameters137 where
  full := (128292392177/1000000000000)
  energy := (675501420803/1000000000000)
  cov := (155017144047/500000000000)
  schur := (1022321248377/1000000000000)
  cap := (1102128149/1000000000000)
  W2 := (409718127461/125000000000)
  V := (162865807/500000000000)
  mass := (270033301/1000000000000)
  rootN := (252774757489/250000000000)
  rootB := (6639663091/200000000000)
  rootU := (324233615439/500000000000)
  rootV := (18048036293/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_137.scalar_checked
  centre := fun n hn => lowFull0_137 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy137 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_137.bound (by norm_num) hn lowTIParameters137_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_138 : FrameRectangleCertificate 8000 8250 (529/1000) (1059/2000) lowTIParameters138 where
  full := (64226080809/500000000000)
  energy := (675269743601/1000000000000)
  cov := (38790841483/125000000000)
  schur := (1022511343257/1000000000000)
  cap := (275791019/250000000000)
  W2 := (1637619818037/500000000000)
  V := (20377429/62500000000)
  mass := (54006583/200000000000)
  rootN := (126399128709/125000000000)
  rootB := (8303478473/250000000000)
  rootU := (324311428673/500000000000)
  rootV := (18056546293/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_138.scalar_checked
  centre := fun n hn => lowFull0_138 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy138 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_138.bound (by norm_num) hn lowTIParameters138_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_139 : FrameRectangleCertificate 8000 8250 (1059/2000) (53/100) lowTIParameters139 where
  full := (25722584689/200000000000)
  energy := (168759543219/250000000000)
  cov := (310619175843/1000000000000)
  schur := (1022701516697/1000000000000)
  cap := (552101091/500000000000)
  W2 := (3272739223021/1000000000000)
  V := (65269223/200000000000)
  mass := (135016277/500000000000)
  rootN := (1011287059493/1000000000000)
  rootB := (16614768897/500000000000)
  rootU := (648780825199/1000000000000)
  rootV := (2258131539/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_139.scalar_checked
  centre := fun n hn => lowFull0_139 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy139 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_139.bound (by norm_num) hn lowTIParameters139_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_140 : FrameRectangleCertificate 8000 8250 (53/100) (1061/2000) lowTIParameters140 where
  full := (32193671747/250000000000)
  energy := (134961341713/200000000000)
  cov := (308242402147/1000000000000)
  schur := (507059295731/500000000000)
  cap := (549563807/500000000000)
  W2 := (817560941473/250000000000)
  V := (323849003/1000000000000)
  mass := (135016107/500000000000)
  rootN := (503517276631/500000000000)
  rootB := (16576546791/500000000000)
  rootU := (648941150897/1000000000000)
  rootV := (17995805151/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_140.scalar_checked
  centre := fun n hn => lowFull0_140 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy140 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_140.bound (by norm_num) hn lowTIParameters140_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_141 : FrameRectangleCertificate 8000 8250 (1061/2000) (531/1000) lowTIParameters141 where
  full := (64468730819/500000000000)
  energy := (168643837649/250000000000)
  cov := (308532329143/1000000000000)
  schur := (101430727997/100000000000)
  cap := (220032987/200000000000)
  W2 := (51058644531/15625000000)
  V := (324153609/1000000000000)
  mass := (54006379/200000000000)
  rootN := (8057025873/8000000000)
  rootB := (331687343/10000000000)
  rootU := (324551925473/500000000000)
  rootV := (4501066603/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_141.scalar_checked
  centre := fun n hn => lowFull0_141 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy141 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_141.bound (by norm_num) hn lowTIParameters141_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_142 : FrameRectangleCertificate 8000 8250 (531/1000) (1063/2000) lowTIParameters142 where
  full := (64550628421/500000000000)
  energy := (134868819781/200000000000)
  cov := (15441112817/50000000000)
  schur := (1014496045729/1000000000000)
  cap := (550602249/500000000000)
  W2 := (163263383037/50000000000)
  V := (40557277/125000000000)
  mass := (67507899/250000000000)
  rootN := (1007221944623/1000000000000)
  rootB := (16592200713/500000000000)
  rootU := (649268941909/1000000000000)
  rootV := (9006361863/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_142.scalar_checked
  centre := fun n hn => lowFull0_142 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy142 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_142.bound (by norm_num) hn lowTIParameters142_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_143 : FrameRectangleCertificate 8000 8250 (1063/2000) (133/250) lowTIParameters143 where
  full := (129266082113/1000000000000)
  energy := (674112953423/1000000000000)
  cov := (309112183739/1000000000000)
  schur := (507342444261/500000000000)
  cap := (1102246327/1000000000000)
  W2 := (3262786983587/1000000000000)
  V := (162381411/500000000000)
  mass := (135015657/500000000000)
  rootN := (1007315684641/1000000000000)
  rootB := (33200095287/1000000000000)
  rootU := (324718220207/500000000000)
  rootV := (18021177043/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_143.scalar_checked
  centre := fun n hn => lowFull0_143 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy143 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_143.bound (by norm_num) hn lowTIParameters143_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_144 : FrameRectangleCertificate 8000 8250 (133/250) (213/400) lowTIParameters144 where
  full := (129431947029/1000000000000)
  energy := (336940957041/500000000000)
  cov := (309402111343/1000000000000)
  schur := (1014873808151/1000000000000)
  cap := (551645221/500000000000)
  W2 := (3260311204047/1000000000000)
  V := (325067429/1000000000000)
  mass := (5400621/20000000000)
  rootN := (1007409454071/1000000000000)
  rootB := (33215816143/1000000000000)
  rootU := (324803181581/500000000000)
  rootV := (721185057/40000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_144.scalar_checked
  centre := fun n hn => lowFull0_144 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy144 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_144.bound (by norm_num) hn lowTIParameters144_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_145 : FrameRectangleCertificate 8000 8250 (213/400) (533/1000) lowTIParameters145 where
  full := (16199857653/125000000000)
  energy := (673650980819/1000000000000)
  cov := (77423009787/250000000000)
  schur := (507531402207/500000000000)
  cap := (1104336863/1000000000000)
  W2 := (1628920153867/500000000000)
  V := (81343009/250000000000)
  mass := (135015401/500000000000)
  rootN := (503751626403/500000000000)
  rootB := (16615782129/500000000000)
  rootU := (649778726901/1000000000000)
  rootV := (18038071849/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_145.scalar_checked
  centre := fun n hn => lowFull0_145 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy145 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_145.bound (by norm_num) hn lowTIParameters145_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_146 : FrameRectangleCertificate 8000 8250 (533/1000) (1067/2000) lowTIParameters146 where
  full := (129766834409/1000000000000)
  energy := (336710076781/500000000000)
  cov := (309981967157/1000000000000)
  schur := (1015251877089/1000000000000)
  cap := (221077123/200000000000)
  W2 := (813843570057/250000000000)
  V := (81419161/250000000000)
  mass := (33753821/125000000000)
  rootN := (1007597080727/1000000000000)
  rootB := (33247339969/1000000000000)
  rootU := (129990709693/200000000000)
  rootV := (4511628337/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_146.scalar_checked
  centre := fun n hn => lowFull0_146 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy146 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_146.bound (by norm_num) hn lowTIParameters146_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_147 : FrameRectangleCertificate 8000 8250 (1067/2000) (267/500) lowTIParameters147 where
  full := (129935876351/1000000000000)
  energy := (2692757729/4000000000)
  cov := (310271895367/1000000000000)
  schur := (253860256499/250000000000)
  cap := (221287343/200000000000)
  W2 := (813228276827/250000000000)
  V := (325981251/1000000000000)
  mass := (270030349/1000000000000)
  rootN := (1007690937737/1000000000000)
  rootB := (33263143493/1000000000000)
  rootU := (162532711187/250000000000)
  rootV := (18054950873/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_147.scalar_checked
  centre := fun n hn => lowFull0_147 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy147 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_147.bound (by norm_num) hn lowTIParameters147_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_148 : FrameRectangleCertificate 8000 8250 (267/500) (1069/2000) lowTIParameters148 where
  full := (65052998441/500000000000)
  energy := (168239704203/250000000000)
  cov := (310561823777/1000000000000)
  schur := (126953781363/125000000000)
  cap := (110749019/100000000000)
  W2 := (3250456774647/1000000000000)
  V := (326285859/1000000000000)
  mass := (135015071/500000000000)
  rootN := (31493275741/31250000000)
  rootB := (6655795039/200000000000)
  rootU := (650310632689/1000000000000)
  rootV := (4515846121/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_148.scalar_checked
  centre := fun n hn => lowFull0_148 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy148 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_148.bound (by norm_num) hn lowTIParameters148_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_149 : FrameRectangleCertificate 8000 8250 (1069/2000) (107/200) lowTIParameters149 where
  full := (130277205901/1000000000000)
  energy := (336364153591/500000000000)
  cov := (155425876193/500000000000)
  schur := (253954887903/250000000000)
  cap := (55427303/50000000000)
  W2 := (3248005268067/1000000000000)
  V := (326590467/1000000000000)
  mass := (67507487/250000000000)
  rootN := (503939369273/500000000000)
  rootB := (4161854417/125000000000)
  rootU := (130098585861/200000000000)
  rootV := (225897677/12500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_149.scalar_checked
  centre := fun n hn => lowFull0_149 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy149 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_149.bound (by norm_num) hn lowTIParameters149_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_150 : FrameRectangleCertificate 8000 8250 (107/200) (1071/2000) lowTIParameters150 where
  full := (32612378343/250000000000)
  energy := (10507779739/15625000000)
  cov := (777854203/2500000000)
  schur := (127001115993/125000000000)
  cap := (1109604347/1000000000000)
  W2 := (5071185271/1562500000)
  V := (13075803/40000000000)
  mass := (135014883/500000000000)
  rootN := (503986341071/500000000000)
  rootB := (6662144841/200000000000)
  rootU := (162669437919/250000000000)
  rootV := (3616047981/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_150.scalar_checked
  centre := fun n hn => lowFull0_150 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy150 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_150.bound (by norm_num) hn lowTIParameters150_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_151 : FrameRectangleCertificate 8000 8250 (1071/2000) (67/125) lowTIParameters151 where
  full := (4081966541/31250000000)
  energy := (134453521017/200000000000)
  cov := (9732237819/31250000000)
  schur := (1016198379663/1000000000000)
  cap := (555332537/500000000000)
  W2 := (1621558338347/500000000000)
  V := (81799921/250000000000)
  mass := (135014797/500000000000)
  rootN := (126008331797/125000000000)
  rootB := (16663321053/500000000000)
  rootU := (650865116911/1000000000000)
  rootV := (18088661753/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_151.scalar_checked
  centre := fun n hn => lowFull0_151 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy151 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_151.bound (by norm_num) hn lowTIParameters151_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_152 : FrameRectangleCertificate 8000 8250 (67/125) (1073/2000) lowTIParameters152 where
  full := (32699365957/250000000000)
  energy := (336018706243/500000000000)
  cov := (311721539417/1000000000000)
  schur := (203277581319/200000000000)
  cap := (55586413/50000000000)
  W2 := (3240679563797/1000000000000)
  V := (81876073/250000000000)
  mass := (33753679/125000000000)
  rootN := (63010040947/62500000000)
  rootB := (16671294641/500000000000)
  rootU := (651055042239/1000000000000)
  rootV := (9048539827/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_152.scalar_checked
  centre := fun n hn => lowFull0_152 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy152 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_152.bound (by norm_num) hn lowTIParameters152_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_153 : FrameRectangleCertificate 8000 8250 (1073/2000) (537/1000) lowTIParameters153 where
  full := (130973127071/1000000000000)
  energy := (167951831357/250000000000)
  cov := (39001433603/125000000000)
  schur := (203315501703/200000000000)
  cap := (556396967/500000000000)
  W2 := (3238247220733/1000000000000)
  V := (327808901/1000000000000)
  mass := (1687683/6250000000)
  rootN := (1008254684351/1000000000000)
  rootB := (33358566127/1000000000000)
  rootU := (651247544893/1000000000000)
  rootV := (1810549367/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_153.scalar_checked
  centre := fun n hn => lowFull0_153 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy153 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_153.bound (by norm_num) hn lowTIParameters153_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_154 : FrameRectangleCertificate 8000 8250 (537/1000) (43/80) lowTIParameters154 where
  full := (65574964629/500000000000)
  energy := (13431546877/20000000000)
  cov := (312301398431/1000000000000)
  schur := (1016767185257/1000000000000)
  cap := (556931057/500000000000)
  W2 := (3235819633647/1000000000000)
  V := (32811351/100000000000)
  mass := (270029137/1000000000000)
  rootN := (1008348741883/1000000000000)
  rootB := (33374572867/1000000000000)
  rootU := (2544697821/3906250000)
  rootV := (566059493/31250000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_154.scalar_checked
  centre := fun n hn => lowFull0_154 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy154 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_154.bound (by norm_num) hn lowTIParameters154_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_155 : FrameRectangleCertificate 8000 8250 (43/80) (269/500) lowTIParameters155 where
  full := (65663940343/500000000000)
  energy := (671347467681/1000000000000)
  cov := (156295664117/500000000000)
  schur := (203391387317/200000000000)
  cap := (44597313/40000000000)
  W2 := (1616698394307/500000000000)
  V := (328418119/1000000000000)
  mass := (135014501/500000000000)
  rootN := (126055353453/125000000000)
  rootB := (33390609833/1000000000000)
  rootU := (40727521967/62500000000)
  rootV := (906115499/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_155.scalar_checked
  centre := fun n hn => lowFull0_155 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy155 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_155.bound (by norm_num) hn lowTIParameters155_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_156 : FrameRectangleCertificate 8000 8250 (269/500) (1077/2000) lowTIParameters156 where
  full := (32876747927/250000000000)
  energy := (33555884843/50000000000)
  cov := (62576251647/200000000000)
  schur := (203429352467/200000000000)
  cap := (139500761/125000000000)
  W2 := (3230978671869/1000000000000)
  V := (328722729/1000000000000)
  mass := (67507219/250000000000)
  rootN := (1008536941483/1000000000000)
  rootB := (33406677297/1000000000000)
  rootU := (20370021569/31250000000)
  rootV := (9065356157/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_156.scalar_checked
  centre := fun n hn => lowFull0_156 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy156 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_156.bound (by norm_num) hn lowTIParameters156_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_157 : FrameRectangleCertificate 8000 8250 (1077/2000) (539/1000) lowTIParameters157 where
  full := (16460909093/125000000000)
  energy := (670888031319/1000000000000)
  cov := (313171188433/1000000000000)
  schur := (1017336662297/1000000000000)
  cap := (111708193/100000000000)
  W2 := (100892664677/31250000000)
  V := (164513669/500000000000)
  mass := (67507189/250000000000)
  rootN := (1008631083349/1000000000000)
  rootB := (16711387809/500000000000)
  rootU := (652043675867/1000000000000)
  rootV := (2267388841/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_157.scalar_checked
  centre := fun n hn => lowFull0_157 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy157 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_157.bound (by norm_num) hn lowTIParameters157_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_158 : FrameRectangleCertificate 8000 8250 (539/1000) (1079/2000) lowTIParameters158 where
  full := (131868734287/1000000000000)
  energy := (670658470991/1000000000000)
  cov := (12538444753/40000000000)
  schur := (1017526636263/1000000000000)
  cap := (1118160371/1000000000000)
  W2 := (3226156568253/1000000000000)
  V := (82332987/250000000000)
  mass := (67507161/250000000000)
  rootN := (1008725253111/1000000000000)
  rootB := (33438905051/1000000000000)
  rootU := (326124663/500000000)
  rootV := (4536876321/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_158.scalar_checked
  centre := fun n hn => lowFull0_158 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy158 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_158.bound (by norm_num) hn lowTIParameters158_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle0_159 : FrameRectangleCertificate 8000 8250 (1079/2000) (27/50) lowTIParameters159 where
  full := (66025693439/500000000000)
  energy := (670429015813/1000000000000)
  cov := (156875524707/500000000000)
  schur := (203543336811/200000000000)
  cap := (223848287/200000000000)
  W2 := (3223752554011/1000000000000)
  V := (164818279/500000000000)
  mass := (135014269/500000000000)
  rootN := (1008819450673/1000000000000)
  rootB := (3345506591/100000000000)
  rootU := (326228829087/500000000000)
  rootV := (18155895957/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness0_159.scalar_checked
  centre := fun n hn => lowFull0_159 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy159 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness0_159.bound (by norm_num) hn lowTIParameters159_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangles0 (j : Fin 160) :
    FrameRectangleCertificate 8000 8250 (frameNoiseLower j) (frameNoiseUpper j) (lowTIParameters j) := by
  match j with
  | ⟨0,_⟩ => convert lowRectangle0_0 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨1,_⟩ => convert lowRectangle0_1 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨2,_⟩ => convert lowRectangle0_2 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨3,_⟩ => convert lowRectangle0_3 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨4,_⟩ => convert lowRectangle0_4 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨5,_⟩ => convert lowRectangle0_5 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨6,_⟩ => convert lowRectangle0_6 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨7,_⟩ => convert lowRectangle0_7 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨8,_⟩ => convert lowRectangle0_8 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨9,_⟩ => convert lowRectangle0_9 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨10,_⟩ => convert lowRectangle0_10 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨11,_⟩ => convert lowRectangle0_11 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨12,_⟩ => convert lowRectangle0_12 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨13,_⟩ => convert lowRectangle0_13 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨14,_⟩ => convert lowRectangle0_14 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨15,_⟩ => convert lowRectangle0_15 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨16,_⟩ => convert lowRectangle0_16 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨17,_⟩ => convert lowRectangle0_17 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨18,_⟩ => convert lowRectangle0_18 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨19,_⟩ => convert lowRectangle0_19 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨20,_⟩ => convert lowRectangle0_20 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨21,_⟩ => convert lowRectangle0_21 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨22,_⟩ => convert lowRectangle0_22 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨23,_⟩ => convert lowRectangle0_23 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨24,_⟩ => convert lowRectangle0_24 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨25,_⟩ => convert lowRectangle0_25 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨26,_⟩ => convert lowRectangle0_26 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨27,_⟩ => convert lowRectangle0_27 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨28,_⟩ => convert lowRectangle0_28 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨29,_⟩ => convert lowRectangle0_29 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨30,_⟩ => convert lowRectangle0_30 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨31,_⟩ => convert lowRectangle0_31 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨32,_⟩ => convert lowRectangle0_32 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨33,_⟩ => convert lowRectangle0_33 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨34,_⟩ => convert lowRectangle0_34 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨35,_⟩ => convert lowRectangle0_35 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨36,_⟩ => convert lowRectangle0_36 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨37,_⟩ => convert lowRectangle0_37 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨38,_⟩ => convert lowRectangle0_38 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨39,_⟩ => convert lowRectangle0_39 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨40,_⟩ => convert lowRectangle0_40 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨41,_⟩ => convert lowRectangle0_41 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨42,_⟩ => convert lowRectangle0_42 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨43,_⟩ => convert lowRectangle0_43 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨44,_⟩ => convert lowRectangle0_44 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨45,_⟩ => convert lowRectangle0_45 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨46,_⟩ => convert lowRectangle0_46 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨47,_⟩ => convert lowRectangle0_47 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨48,_⟩ => convert lowRectangle0_48 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨49,_⟩ => convert lowRectangle0_49 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨50,_⟩ => convert lowRectangle0_50 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨51,_⟩ => convert lowRectangle0_51 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨52,_⟩ => convert lowRectangle0_52 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨53,_⟩ => convert lowRectangle0_53 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨54,_⟩ => convert lowRectangle0_54 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨55,_⟩ => convert lowRectangle0_55 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨56,_⟩ => convert lowRectangle0_56 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨57,_⟩ => convert lowRectangle0_57 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨58,_⟩ => convert lowRectangle0_58 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨59,_⟩ => convert lowRectangle0_59 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨60,_⟩ => convert lowRectangle0_60 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨61,_⟩ => convert lowRectangle0_61 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨62,_⟩ => convert lowRectangle0_62 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨63,_⟩ => convert lowRectangle0_63 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨64,_⟩ => convert lowRectangle0_64 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨65,_⟩ => convert lowRectangle0_65 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨66,_⟩ => convert lowRectangle0_66 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨67,_⟩ => convert lowRectangle0_67 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨68,_⟩ => convert lowRectangle0_68 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨69,_⟩ => convert lowRectangle0_69 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨70,_⟩ => convert lowRectangle0_70 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨71,_⟩ => convert lowRectangle0_71 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨72,_⟩ => convert lowRectangle0_72 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨73,_⟩ => convert lowRectangle0_73 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨74,_⟩ => convert lowRectangle0_74 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨75,_⟩ => convert lowRectangle0_75 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨76,_⟩ => convert lowRectangle0_76 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨77,_⟩ => convert lowRectangle0_77 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨78,_⟩ => convert lowRectangle0_78 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨79,_⟩ => convert lowRectangle0_79 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨80,_⟩ => convert lowRectangle0_80 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨81,_⟩ => convert lowRectangle0_81 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨82,_⟩ => convert lowRectangle0_82 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨83,_⟩ => convert lowRectangle0_83 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨84,_⟩ => convert lowRectangle0_84 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨85,_⟩ => convert lowRectangle0_85 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨86,_⟩ => convert lowRectangle0_86 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨87,_⟩ => convert lowRectangle0_87 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨88,_⟩ => convert lowRectangle0_88 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨89,_⟩ => convert lowRectangle0_89 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨90,_⟩ => convert lowRectangle0_90 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨91,_⟩ => convert lowRectangle0_91 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨92,_⟩ => convert lowRectangle0_92 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨93,_⟩ => convert lowRectangle0_93 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨94,_⟩ => convert lowRectangle0_94 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨95,_⟩ => convert lowRectangle0_95 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨96,_⟩ => convert lowRectangle0_96 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨97,_⟩ => convert lowRectangle0_97 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨98,_⟩ => convert lowRectangle0_98 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨99,_⟩ => convert lowRectangle0_99 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨100,_⟩ => convert lowRectangle0_100 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨101,_⟩ => convert lowRectangle0_101 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨102,_⟩ => convert lowRectangle0_102 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨103,_⟩ => convert lowRectangle0_103 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨104,_⟩ => convert lowRectangle0_104 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨105,_⟩ => convert lowRectangle0_105 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨106,_⟩ => convert lowRectangle0_106 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨107,_⟩ => convert lowRectangle0_107 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨108,_⟩ => convert lowRectangle0_108 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨109,_⟩ => convert lowRectangle0_109 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨110,_⟩ => convert lowRectangle0_110 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨111,_⟩ => convert lowRectangle0_111 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨112,_⟩ => convert lowRectangle0_112 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨113,_⟩ => convert lowRectangle0_113 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨114,_⟩ => convert lowRectangle0_114 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨115,_⟩ => convert lowRectangle0_115 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨116,_⟩ => convert lowRectangle0_116 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨117,_⟩ => convert lowRectangle0_117 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨118,_⟩ => convert lowRectangle0_118 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨119,_⟩ => convert lowRectangle0_119 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨120,_⟩ => convert lowRectangle0_120 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨121,_⟩ => convert lowRectangle0_121 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨122,_⟩ => convert lowRectangle0_122 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨123,_⟩ => convert lowRectangle0_123 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨124,_⟩ => convert lowRectangle0_124 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨125,_⟩ => convert lowRectangle0_125 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨126,_⟩ => convert lowRectangle0_126 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨127,_⟩ => convert lowRectangle0_127 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨128,_⟩ => convert lowRectangle0_128 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨129,_⟩ => convert lowRectangle0_129 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨130,_⟩ => convert lowRectangle0_130 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨131,_⟩ => convert lowRectangle0_131 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨132,_⟩ => convert lowRectangle0_132 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨133,_⟩ => convert lowRectangle0_133 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨134,_⟩ => convert lowRectangle0_134 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨135,_⟩ => convert lowRectangle0_135 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨136,_⟩ => convert lowRectangle0_136 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨137,_⟩ => convert lowRectangle0_137 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨138,_⟩ => convert lowRectangle0_138 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨139,_⟩ => convert lowRectangle0_139 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨140,_⟩ => convert lowRectangle0_140 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨141,_⟩ => convert lowRectangle0_141 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨142,_⟩ => convert lowRectangle0_142 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨143,_⟩ => convert lowRectangle0_143 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨144,_⟩ => convert lowRectangle0_144 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨145,_⟩ => convert lowRectangle0_145 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨146,_⟩ => convert lowRectangle0_146 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨147,_⟩ => convert lowRectangle0_147 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨148,_⟩ => convert lowRectangle0_148 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨149,_⟩ => convert lowRectangle0_149 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨150,_⟩ => convert lowRectangle0_150 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨151,_⟩ => convert lowRectangle0_151 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨152,_⟩ => convert lowRectangle0_152 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨153,_⟩ => convert lowRectangle0_153 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨154,_⟩ => convert lowRectangle0_154 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨155,_⟩ => convert lowRectangle0_155 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨156,_⟩ => convert lowRectangle0_156 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨157,_⟩ => convert lowRectangle0_157 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨158,_⟩ => convert lowRectangle0_158 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨159,_⟩ => convert lowRectangle0_159 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨j+160,h⟩ => exact False.elim (by omega)
end BstLean.BlueprintLow
