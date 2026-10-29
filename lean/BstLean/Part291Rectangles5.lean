import BstLean.Part291Rectangle
import BstLean.Part291Certificates5
import BstLean.Part291LocalEnergyBatch0
import BstLean.Part291LocalEnergyBatch1
namespace BstLean.BlueprintLow
open Real Set BstLean.Part255
noncomputable def lowRectangle5_0 : FrameRectangleCertificate 11000 11882 (23/50) (921/2000) lowTIParameters0 where
  full := (97072520631/1000000000000)
  energy := (44267434443/62500000000)
  cov := (11379015679/40000000000)
  schur := (1044037648499/1000000000000)
  cap := (726564921/1000000000000)
  W2 := (1827121689959/500000000000)
  V := (217366289/1000000000000)
  mass := (1376867/250000000000)
  rootN := (102178160509/100000000000)
  rootB := (1078194729/40000000000)
  rootU := (119117860271/200000000000)
  rootV := (184291841/12500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_0.scalar_checked
  centre := fun n hn => lowFull5_0 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy0 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_0.bound (by norm_num) hn lowTIParameters0_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_1 : FrameRectangleCertificate 11000 11882 (921/2000) (461/1000) lowTIParameters1 where
  full := (24286731191/250000000000)
  energy := (708032000171/1000000000000)
  cov := (17791104233/62500000000)
  schur := (130471080729/125000000000)
  cap := (145402049/200000000000)
  W2 := (3650928806143/1000000000000)
  V := (43501113/200000000000)
  mass := (312741/62500000000)
  rootN := (1021649962479/1000000000000)
  rootB := (6740781877/250000000000)
  rootU := (297773616213/500000000000)
  rootV := (7374034937/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_1.scalar_checked
  centre := fun n hn => lowFull5_1 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy1 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_1.bound (by norm_num) hn lowTIParameters1_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_2 : FrameRectangleCertificate 11000 11882 (461/1000) (923/2000) lowTIParameters2 where
  full := (9722132351/100000000000)
  energy := (353892583027/500000000000)
  cov := (71209938901/250000000000)
  schur := (521749948109/500000000000)
  cap := (145491041/200000000000)
  W2 := (1823810898363/500000000000)
  V := (217644697/1000000000000)
  mass := (4548287/1000000000000)
  rootN := (255379606691/250000000000)
  rootB := (13485688757/500000000000)
  rootU := (595505347367/1000000000000)
  rootV := (3688196519/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_2.scalar_checked
  centre := fun n hn => lowFull5_2 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy2 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_2.bound (by norm_num) hn lowTIParameters2_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_3 : FrameRectangleCertificate 11000 11882 (923/2000) (231/500) lowTIParameters3 where
  full := (12161964613/125000000000)
  energy := (707538448651/1000000000000)
  cov := (142573816291/500000000000)
  schur := (1043692178859/1000000000000)
  cap := (728118333/1000000000000)
  W2 := (145772893029/40000000000)
  V := (43575989/200000000000)
  mass := (4136001/1000000000000)
  rootN := (1021612538519/1000000000000)
  rootB := (13491833947/500000000000)
  rootU := (595463645667/1000000000000)
  rootV := (7380378463/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_3.scalar_checked
  centre := fun n hn => lowFull5_3 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy3 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_3.bound (by norm_num) hn lowTIParameters3_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_4 : FrameRectangleCertificate 11000 11882 (231/500) (37/80) lowTIParameters4 where
  full := (97370104983/1000000000000)
  energy := (707291847877/1000000000000)
  cov := (285203366987/1000000000000)
  schur := (1042963147899/1000000000000)
  cap := (728344043/1000000000000)
  W2 := (3641030367383/1000000000000)
  V := (217922531/1000000000000)
  mass := (3762727/1000000000000)
  rootN := (1021255672151/1000000000000)
  rootB := (5397569983/200000000000)
  rootU := (59542212683/100000000000)
  rootV := (3690549849/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_4.scalar_checked
  centre := fun n hn => lowFull5_4 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy4 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_4.bound (by norm_num) hn lowTIParameters4_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_5 : FrameRectangleCertificate 11000 11882 (37/80) (463/1000) lowTIParameters5 where
  full := (97444487779/1000000000000)
  energy := (176761340913/250000000000)
  cov := (142755485851/500000000000)
  schur := (130394435291/125000000000)
  cap := (3645033/5000000000)
  W2 := (727549179221/200000000000)
  V := (21815757/100000000000)
  mass := (428079/125000000000)
  rootN := (102134983347/100000000000)
  rootB := (13500061111/500000000000)
  rootU := (595380790349/1000000000000)
  rootV := (1477015809/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_5.scalar_checked
  centre := fun n hn => lowFull5_5 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy5 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_5.bound (by norm_num) hn lowTIParameters5_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_6 : FrameRectangleCertificate 11000 11882 (463/1000) (927/2000) lowTIParameters6 where
  full := (9751886533/100000000000)
  energy := (44174937243/62500000000)
  cov := (71391557191/250000000000)
  schur := (104242740229/100000000000)
  cap := (364615719/500000000000)
  W2 := (3634468886323/1000000000000)
  V := (13637487/62500000000)
  mass := (48723/15625000000)
  rootN := (1020993340963/1000000000000)
  rootB := (27004285549/1000000000000)
  rootU := (595339635731/1000000000000)
  rootV := (7385793661/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_6.scalar_checked
  centre := fun n hn => lowFull5_6 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy6 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_6.bound (by norm_num) hn lowTIParameters6_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_7 : FrameRectangleCertificate 11000 11882 (927/2000) (58/125) lowTIParameters7 where
  full := (97593237673/1000000000000)
  energy := (141310548901/200000000000)
  cov := (142936780791/500000000000)
  schur := (1042619786809/1000000000000)
  cap := (29195737/40000000000)
  W2 := (453899914081/125000000000)
  V := (218434623/1000000000000)
  mass := (2840553/1000000000000)
  rootN := (1021087551001/1000000000000)
  rootB := (13508269921/500000000000)
  rootU := (297649331243/500000000000)
  rootV := (3694883481/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_7.scalar_checked
  centre := fun n hn => lowFull5_7 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy7 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_7.bound (by norm_num) hn lowTIParameters7_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_8 : FrameRectangleCertificate 11000 11882 (58/125) (929/2000) lowTIParameters8 where
  full := (24416901211/250000000000)
  energy := (35315330471/50000000000)
  cov := (28592834129/100000000000)
  schur := (520946324927/500000000000)
  cap := (730117391/1000000000000)
  W2 := (1813968574927/500000000000)
  V := (682739/3125000000)
  mass := (517739/200000000000)
  rootN := (127591428607/125000000000)
  rootB := (27020684503/1000000000000)
  rootU := (59525787013/100000000000)
  rootV := (7390474951/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_8.scalar_checked
  centre := fun n hn => lowFull5_8 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy8 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_8.bound (by norm_num) hn lowTIParameters8_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_9 : FrameRectangleCertificate 11000 11882 (929/2000) (93/200) lowTIParameters9 where
  full := (610887293/6250000000)
  energy := (353030295273/500000000000)
  cov := (286235402571/1000000000000)
  schur := (1042085082807/1000000000000)
  cap := (182694703/250000000000)
  W2 := (56635662073/15625000000)
  V := (3417361/15625000000)
  mass := (2360197/1000000000000)
  rootN := (1020825686789/1000000000000)
  rootB := (27032920893/1000000000000)
  rootU := (74402157271/125000000000)
  rootV := (591555379/40000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_9.scalar_checked
  centre := fun n hn => lowFull5_9 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy9 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_9.bound (by norm_num) hn lowTIParameters9_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_10 : FrameRectangleCertificate 11000 11882 (93/200) (931/2000) lowTIParameters10 where
  full := (48908161909/500000000000)
  energy := (705814687803/1000000000000)
  cov := (286289705349/1000000000000)
  schur := (520679441343/500000000000)
  cap := (365500953/500000000000)
  W2 := (3621434956079/1000000000000)
  V := (218752597/1000000000000)
  mass := (2152807/1000000000000)
  rootN := (25511748307/25000000000)
  rootB := (13518523459/500000000000)
  rootU := (14879420653/25000000000)
  rootV := (14790287253/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_10.scalar_checked
  centre := fun n hn => lowFull5_10 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy10 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_10.bound (by norm_num) hn lowTIParameters10_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_11 : FrameRectangleCertificate 11000 11882 (931/2000) (233/500) lowTIParameters11 where
  full := (48945337849/500000000000)
  energy := (705568901107/1000000000000)
  cov := (8956140483/31250000000)
  schur := (8137120019/7812500000)
  cap := (731662761/1000000000000)
  W2 := (1809097437583/500000000000)
  V := (109493507/500000000000)
  mass := (1964501/1000000000000)
  rootN := (1020564237289/1000000000000)
  rootB := (27049265443/1000000000000)
  rootU := (595136573517/1000000000000)
  rootV := (591928393/40000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_11.scalar_checked
  centre := fun n hn => lowFull5_11 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy11 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_11.bound (by norm_num) hn lowTIParameters11_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_12 : FrameRectangleCertificate 11000 11882 (233/500) (933/2000) lowTIParameters12 where
  full := (24491255639/250000000000)
  energy := (88165403797/125000000000)
  cov := (143325161099/500000000000)
  schur := (1040826094727/1000000000000)
  cap := (731884987/1000000000000)
  W2 := (1807481052523/500000000000)
  V := (219028143/1000000000000)
  mass := (358691/200000000000)
  rootN := (1020208848583/1000000000000)
  rootB := (27053372933/1000000000000)
  rootU := (595096499873/1000000000000)
  rootV := (14799599421/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_12.scalar_checked
  centre := fun n hn => lowFull5_12 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy12 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_12.bound (by norm_num) hn lowTIParameters12_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_13 : FrameRectangleCertificate 11000 11882 (933/2000) (467/1000) lowTIParameters13 where
  full := (98039364433/1000000000000)
  energy := (352538837763/500000000000)
  cov := (286956841491/1000000000000)
  schur := (52050930981/50000000000)
  cap := (183136319/250000000000)
  W2 := (3611736621033/1000000000000)
  V := (13703897/62500000000)
  mass := (204753/125000000000)
  rootN := (127537899981/125000000000)
  rootB := (105724897/3906250000)
  rootU := (148764151181/250000000000)
  rootV := (14807509987/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_13.scalar_checked
  centre := fun n hn => lowFull5_13 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy13 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_13.bound (by norm_num) hn lowTIParameters13_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_14 : FrameRectangleCertificate 11000 11882 (467/1000) (187/400) lowTIParameters14 where
  full := (12264212671/125000000000)
  energy := (704832236477/1000000000000)
  cov := (287010193061/1000000000000)
  schur := (8127299061/7812500000)
  cap := (366383317/500000000000)
  W2 := (72170367971/20000000000)
  V := (109651559/500000000000)
  mass := (1496729/1000000000000)
  rootN := (50997408753/50000000000)
  rootB := (13534831307/500000000000)
  rootU := (297508443803/500000000000)
  rootV := (7404443227/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_14.scalar_checked
  centre := fun n hn => lowFull5_14 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy14 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_14.bound (by norm_num) hn lowTIParameters14_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_15 : FrameRectangleCertificate 11000 11882 (187/400) (117/250) lowTIParameters15 where
  full := (490940167/5000000000)
  energy := (88073364143/125000000000)
  cov := (2873164419/10000000000)
  schur := (1040486848257/1000000000000)
  cap := (733426361/1000000000000)
  W2 := (721061482609/200000000000)
  V := (219537121/1000000000000)
  mass := (684117/500000000000)
  rootN := (1020042571787/1000000000000)
  rootB := (27081845599/1000000000000)
  rootU := (37186084253/62500000000)
  rootV := (14816785111/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_15.scalar_checked
  centre := fun n hn => lowFull5_15 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy15 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_15.bound (by norm_num) hn lowTIParameters15_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_16 : FrameRectangleCertificate 11000 11882 (117/250) (937/2000) lowTIParameters16 where
  full := (9826236057/100000000000)
  energy := (140868341089/200000000000)
  cov := (143684659357/500000000000)
  schur := (519881715117/500000000000)
  cap := (733646853/1000000000000)
  W2 := (180105182007/50000000000)
  V := (54894381/250000000000)
  mass := (625667/500000000000)
  rootN := (254921977063/250000000000)
  rootB := (13542958069/500000000000)
  rootU := (594937985591/1000000000000)
  rootV := (3704537117/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_16.scalar_checked
  centre := fun n hn => lowFull5_16 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy16 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_16.bound (by norm_num) hn lowTIParameters16_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_17 : FrameRectangleCertificate 11000 11882 (937/2000) (469/1000) lowTIParameters17 where
  full := (98336682917/1000000000000)
  energy := (704096613301/1000000000000)
  cov := (287675297457/1000000000000)
  schur := (259989010163/250000000000)
  cap := (367153009/500000000000)
  W2 := (3598907055609/1000000000000)
  V := (219811321/1000000000000)
  mass := (572471/500000000000)
  rootN := (63736396853/62500000000)
  rootB := (13549040723/500000000000)
  rootU := (594898799777/1000000000000)
  rootV := (14826035243/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_17.scalar_checked
  centre := fun n hn => lowFull5_17 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy17 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_17.bound (by norm_num) hn lowTIParameters17_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_18 : FrameRectangleCertificate 11000 11882 (469/1000) (939/2000) lowTIParameters18 where
  full := (49205500243/500000000000)
  energy := (703851636627/1000000000000)
  cov := (143863850183/500000000000)
  schur := (519616769981/500000000000)
  cap := (734525647/1000000000000)
  W2 := (1797858817613/500000000000)
  V := (109925681/500000000000)
  mass := (524039/500000000000)
  rootN := (203885609101/200000000000)
  rootB := (216817069/8000000000)
  rootU := (594859790159/1000000000000)
  rootV := (7413692771/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_18.scalar_checked
  centre := fun n hn => lowFull5_18 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy18 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_18.bound (by norm_num) hn lowTIParameters18_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_19 : FrameRectangleCertificate 11000 11882 (939/2000) (47/100) lowTIParameters19 where
  full := (24621328329/250000000000)
  energy := (351803387671/500000000000)
  cov := (288033409369/1000000000000)
  schur := (1039426190767/1000000000000)
  cap := (2940737/4000000000)
  W2 := (3592535355003/1000000000000)
  V := (220084953/1000000000000)
  mass := (479927/500000000000)
  rootN := (50976126539/50000000000)
  rootB := (27114281293/1000000000000)
  rootU := (297410478143/500000000000)
  rootV := (14835260463/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_19.scalar_checked
  centre := fun n hn => lowFull5_19 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy19 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_19.bound (by norm_num) hn lowTIParameters19_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_20 : FrameRectangleCertificate 11000 11882 (47/100) (941/2000) lowTIParameters20 where
  full := (12319952681/125000000000)
  energy := (703362029363/1000000000000)
  cov := (288085338767/1000000000000)
  schur := (129838075167/125000000000)
  cap := (735403017/1000000000000)
  W2 := (3589360190907/1000000000000)
  V := (27515579/125000000000)
  mass := (87947/100000000000)
  rootN := (509584291687/500000000000)
  rootB := (13559157579/500000000000)
  rootU := (5947822977/10000000000)
  rootV := (3709149431/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_20.scalar_checked
  centre := fun n hn => lowFull5_20 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy20 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_20.bound (by norm_num) hn lowTIParameters20_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_21 : FrameRectangleCertificate 11000 11882 (941/2000) (471/1000) lowTIParameters21 where
  full := (1541155077/15625000000)
  energy := (175779349653/250000000000)
  cov := (144195389193/500000000000)
  schur := (259724322747/250000000000)
  cap := (736061061/1000000000000)
  W2 := (3586192119207/1000000000000)
  V := (220358017/1000000000000)
  mass := (403101/500000000000)
  rootN := (1019263111757/1000000000000)
  rootB := (27130445279/1000000000000)
  rootU := (594743813977/1000000000000)
  rootV := (14844460819/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_21.scalar_checked
  centre := fun n hn => lowFull5_21 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy21 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_21.bound (by norm_num) hn lowTIParameters21_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_22 : FrameRectangleCertificate 11000 11882 (471/1000) (943/2000) lowTIParameters22 where
  full := (98708223797/1000000000000)
  energy := (702872883003/1000000000000)
  cov := (288696218237/1000000000000)
  schur := (1039090084719/1000000000000)
  cap := (368359521/500000000000)
  W2 := (179151555803/50000000000)
  V := (110295701/500000000000)
  mass := (147879/200000000000)
  rootN := (509678841213/500000000000)
  rootB := (13571284409/500000000000)
  rootU := (594705504663/1000000000000)
  rootV := (1856539969/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_22.scalar_checked
  centre := fun n hn => lowFull5_22 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy22 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_22.bound (by norm_num) hn lowTIParameters22_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_23 : FrameRectangleCertificate 11000 11882 (943/2000) (59/125) lowTIParameters23 where
  full := (987825181/10000000000)
  energy := (702628482457/1000000000000)
  cov := (57800331663/200000000000)
  schur := (207856596437/200000000000)
  cap := (184344239/250000000000)
  W2 := (3579877157883/1000000000000)
  V := (220824787/1000000000000)
  mass := (339229/500000000000)
  rootN := (1019452295199/1000000000000)
  rootB := (2715468571/100000000000)
  rootU := (594667369329/1000000000000)
  rootV := (232190227/15625000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_23.scalar_checked
  centre := fun n hn => lowFull5_23 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy23 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_23.bound (by norm_num) hn lowTIParameters23_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_24 : FrameRectangleCertificate 11000 11882 (59/125) (189/400) lowTIParameters24 where
  full := (98856807881/1000000000000)
  energy := (140476839379/200000000000)
  cov := (289307098621/1000000000000)
  schur := (1039475983059/1000000000000)
  cap := (369017403/500000000000)
  W2 := (111772819413/31250000000)
  V := (221058173/1000000000000)
  mass := (124571/200000000000)
  rootN := (203909389981/200000000000)
  rootB := (27166796021/1000000000000)
  rootU := (594629407549/1000000000000)
  rootV := (14868025189/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_24.scalar_checked
  centre := fun n hn => lowFull5_24 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy24 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_24.bound (by norm_num) hn lowTIParameters24_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_25 : FrameRectangleCertificate 11000 11882 (189/400) (473/1000) lowTIParameters25 where
  full := (1545798331/15625000000)
  energy := (351070013117/500000000000)
  cov := (57922507831/200000000000)
  schur := (1039669086983/1000000000000)
  cap := (738692591/1000000000000)
  W2 := (1786795141287/500000000000)
  V := (110645779/500000000000)
  mass := (5721/10000000000)
  rootN := (254910411589/250000000000)
  rootB := (27178899739/1000000000000)
  rootU := (148647904721/250000000000)
  rootV := (1859483959/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_25.scalar_checked
  centre := fun n hn => lowFull5_25 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy25 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_25.bound (by norm_num) hn lowTIParameters25_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_26 : FrameRectangleCertificate 11000 11882 (473/1000) (947/2000) lowTIParameters26 where
  full := (19801074811/200000000000)
  energy := (350947985197/500000000000)
  cov := (144958989959/500000000000)
  schur := (103986229363/100000000000)
  cap := (92418789/125000000000)
  W2 := (714091463737/200000000000)
  V := (13845309/62500000000)
  mass := (105151/200000000000)
  rootN := (1019736384381/1000000000000)
  rootB := (27190996893/1000000000000)
  rootU := (594554002917/1000000000000)
  rootV := (14883714053/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_26.scalar_checked
  centre := fun n hn => lowFull5_26 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy26 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_26.bound (by norm_num) hn lowTIParameters26_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_27 : FrameRectangleCertificate 11000 11882 (947/2000) (237/500) lowTIParameters27 where
  full := (99079650539/1000000000000)
  energy := (701652029291/1000000000000)
  cov := (290223420911/1000000000000)
  schur := (130006950331/125000000000)
  cap := (23125249/31250000000)
  W2 := (891832826573/250000000000)
  V := (22175833/100000000000)
  mass := (483421/1000000000000)
  rootN := (254957790949/250000000000)
  rootB := (1700192967/62500000000)
  rootU := (297258279609/500000000000)
  rootV := (930722019/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_27.scalar_checked
  centre := fun n hn => lowFull5_27 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy27 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_27.bound (by norm_num) hn lowTIParameters27_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_28 : FrameRectangleCertificate 11000 11882 (237/500) (949/2000) lowTIParameters28 where
  full := (24788480671/250000000000)
  energy := (701408202847/1000000000000)
  cov := (290528862127/1000000000000)
  schur := (208049802737/200000000000)
  cap := (370332781/500000000000)
  W2 := (1782106111153/500000000000)
  V := (55497929/250000000000)
  mass := (444737/1000000000000)
  rootN := (31872687013/31250000000)
  rootB := (27215171541/1000000000000)
  rootU := (594479287377/1000000000000)
  rootV := (14899386431/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_28.scalar_checked
  centre := fun n hn => lowFull5_28 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy28 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_28.bound (by norm_num) hn lowTIParameters28_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_29 : FrameRectangleCertificate 11000 11882 (949/2000) (19/40) lowTIParameters29 where
  full := (12403523817/125000000000)
  energy := (87645561373/125000000000)
  cov := (72708575893/250000000000)
  schur := (520221263221/500000000000)
  cap := (74132309/100000000000)
  W2 := (890275010951/250000000000)
  V := (222225103/1000000000000)
  mass := (409377/1000000000000)
  rootN := (1020020846083/1000000000000)
  rootB := (5445449807/200000000000)
  rootU := (594442186983/1000000000000)
  rootV := (7453608237/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_29.scalar_checked
  centre := fun n hn => lowFull5_29 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy29 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_29.bound (by norm_num) hn lowTIParameters29_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_30 : FrameRectangleCertificate 11000 11882 (19/40) (951/2000) lowTIParameters30 where
  full := (99302454143/1000000000000)
  energy := (350460446809/500000000000)
  cov := (72784936311/250000000000)
  schur := (520318070283/500000000000)
  cap := (370990277/500000000000)
  W2 := (3557994747813/1000000000000)
  V := (222458489/1000000000000)
  mass := (94261/250000000000)
  rootN := (255028937153/250000000000)
  rootB := (27239319999/1000000000000)
  rootU := (29720262881/50000000000)
  rootV := (7457521187/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_30.scalar_checked
  centre := fun n hn => lowFull5_30 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy30 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_30.bound (by norm_num) hn lowTIParameters30_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_31 : FrameRectangleCertificate 11000 11882 (951/2000) (119/250) lowTIParameters31 where
  full := (49688356777/500000000000)
  energy := (700677410671/1000000000000)
  cov := (14572259357/50000000000)
  schur := (520414927863/500000000000)
  cap := (742637957/1000000000000)
  W2 := (444362038949/125000000000)
  V := (55672969/250000000000)
  mass := (347467/1000000000000)
  rootN := (1020210691831/1000000000000)
  rootB := (27251384497/1000000000000)
  rootU := (594368498889/1000000000000)
  rootV := (14922864203/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_31.scalar_checked
  centre := fun n hn => lowFull5_31 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy31 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_31.bound (by norm_num) hn lowTIParameters31_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_32 : FrameRectangleCertificate 11000 11882 (119/250) (953/2000) lowTIParameters32 where
  full := (6215685551/62500000000)
  energy := (350217021031/500000000000)
  cov := (145875314631/500000000000)
  schur := (1041023671579/1000000000000)
  cap := (148659059/200000000000)
  W2 := (355180471239/100000000000)
  V := (222925263/1000000000000)
  mass := (80101/250000000000)
  rootN := (25507641889/25000000000)
  rootB := (5452688493/200000000000)
  rootU := (297165955189/500000000000)
  rootV := (7465340967/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_32.scalar_checked
  centre := fun n hn => lowFull5_32 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy32 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_32.bound (by norm_num) hn lowTIParameters32_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_33 : FrameRectangleCertificate 11000 11882 (953/2000) (477/1000) lowTIParameters33 where
  full := (4976260999/50000000000)
  energy := (700190787709/1000000000000)
  cov := (292056071609/1000000000000)
  schur := (1041217587803/1000000000000)
  cap := (92994071/125000000000)
  W2 := (3548719927621/1000000000000)
  V := (4463173/20000000000)
  mass := (295633/1000000000000)
  rootN := (1020400699629/1000000000000)
  rootB := (2727549391/100000000000)
  rootU := (594295491691/1000000000000)
  rootV := (7469247787/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_33.scalar_checked
  centre := fun n hn => lowFull5_33 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy33 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_33.bound (by norm_num) hn lowTIParameters33_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_34 : FrameRectangleCertificate 11000 11882 (477/1000) (191/400) lowTIParameters34 where
  full := (19919893419/200000000000)
  energy := (349973823769/500000000000)
  cov := (292361514179/1000000000000)
  schur := (130176450509/125000000000)
  cap := (744609779/1000000000000)
  W2 := (88641048371/25000000000)
  V := (223392037/1000000000000)
  mass := (5459/20000000000)
  rootN := (255123940967/250000000000)
  rootB := (1705471181/62500000000)
  rootU := (148564810609/250000000000)
  rootV := (14946305129/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_34.scalar_checked
  centre := fun n hn => lowFull5_34 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy34 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_34.bound (by norm_num) hn lowTIParameters34_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_35 : FrameRectangleCertificate 11000 11882 (191/400) (239/500) lowTIParameters35 where
  full := (24918427553/250000000000)
  energy := (349852310731/500000000000)
  cov := (292666956977/1000000000000)
  schur := (208321144013/200000000000)
  cap := (745266927/1000000000000)
  W2 := (708514142319/200000000000)
  V := (13976589/62500000000)
  mass := (126087/500000000000)
  rootN := (255147717027/250000000000)
  rootB := (5459915483/200000000000)
  rootU := (74277895277/125000000000)
  rootV := (7477055303/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_35.scalar_checked
  centre := fun n hn => lowFull5_35 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy35 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_35.bound (by norm_num) hn lowTIParameters35_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_36 : FrameRectangleCertificate 11000 11882 (239/500) (957/2000) lowTIParameters36 where
  full := (49873974691/500000000000)
  energy := (699461709407/1000000000000)
  cov := (73243099999/250000000000)
  schur := (520899967723/500000000000)
  cap := (745924011/1000000000000)
  W2 := (884876558909/250000000000)
  V := (55964703/250000000000)
  mass := (116569/500000000000)
  rootN := (510343006087/500000000000)
  rootB := (5462321891/200000000000)
  rootU := (297093625323/500000000000)
  rootV := (3740478011/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_36.scalar_checked
  centre := fun n hn => lowFull5_36 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy36 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_36.bound (by norm_num) hn lowTIParameters36_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_37 : FrameRectangleCertificate 11000 11882 (957/2000) (479/1000) lowTIParameters37 where
  full := (49911092329/500000000000)
  energy := (699218911291/1000000000000)
  cov := (73319460809/250000000000)
  schur := (208398849977/200000000000)
  cap := (746581033/1000000000000)
  W2 := (3536448484751/1000000000000)
  V := (1120461/5000000000)
  mass := (215691/1000000000000)
  rootN := (255195298973/250000000000)
  rootB := (13661817531/500000000000)
  rootU := (37134469209/62500000000)
  rootV := (14969709417/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_37.scalar_checked
  centre := fun n hn => lowFull5_37 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy37 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_37.bound (by norm_num) hn lowTIParameters37_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_38 : FrameRectangleCertificate 11000 11882 (479/1000) (959/2000) lowTIParameters38 where
  full := (9989641609/100000000000)
  energy := (349488113519/500000000000)
  cov := (146791643351/500000000000)
  schur := (208437732621/200000000000)
  cap := (93404749/125000000000)
  W2 := (706679487377/200000000000)
  V := (56081397/250000000000)
  mass := (99847/500000000000)
  rootN := (204175283823/200000000000)
  rootB := (27335654227/1000000000000)
  rootU := (23764637277/40000000000)
  rootV := (1497750273/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_38.scalar_checked
  centre := fun n hn => lowFull5_38 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy38 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_38.bound (by norm_num) hn lowTIParameters38_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_39 : FrameRectangleCertificate 11000 11882 (959/2000) (12/25) lowTIParameters39 where
  full := (49985321867/500000000000)
  energy := (139746731313/200000000000)
  cov := (293888730389/1000000000000)
  schur := (52119158737/50000000000)
  cap := (747894889/1000000000000)
  W2 := (882588267493/250000000000)
  V := (1754367/7812500000)
  mass := (92511/500000000000)
  rootN := (204194336331/200000000000)
  rootB := (854614593/31250000000)
  rootU := (118816104803/200000000000)
  rootV := (1498529199/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_39.scalar_checked
  centre := fun n hn => lowFull5_39 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy39 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_39.bound (by norm_num) hn lowTIParameters39_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_40 : FrameRectangleCertificate 11000 11882 (12/25) (961/2000) lowTIParameters40 where
  full := (50022433821/500000000000)
  energy := (698491199793/1000000000000)
  cov := (291621074777/1000000000000)
  schur := (129183270147/125000000000)
  cap := (744099097/1000000000000)
  W2 := (881828840527/250000000000)
  V := (222826271/1000000000000)
  mass := (85781/500000000000)
  rootN := (508297688657/500000000000)
  rootB := (2727817987/100000000000)
  rootU := (118809056647/200000000000)
  rootV := (14927366513/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_40.scalar_checked
  centre := fun n hn => lowFull5_40 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy40 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_40.bound (by norm_num) hn lowTIParameters40_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_41 : FrameRectangleCertificate 11000 11882 (961/2000) (481/1000) lowTIParameters41 where
  full := (100119087869/1000000000000)
  energy := (698248856647/1000000000000)
  cov := (5838476797/20000000000)
  schur := (1292073947/1250000000)
  cap := (148950323/200000000000)
  W2 := (3524284291527/1000000000000)
  V := (55764403/250000000000)
  mass := (19901/125000000000)
  rootN := (1016690295813/1000000000000)
  rootB := (3411267211/125000000000)
  rootU := (594010209221/1000000000000)
  rootV := (14935113391/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_41.scalar_checked
  centre := fun n hn => lowFull5_41 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy41 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_41.bound (by norm_num) hn lowTIParameters41_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_42 : FrameRectangleCertificate 11000 11882 (481/1000) (963/2000) lowTIParameters42 where
  full := (100193304471/1000000000000)
  energy := (349003313523/500000000000)
  cov := (58445321029/200000000000)
  schur := (129231531333/125000000000)
  cap := (74540407/100000000000)
  W2 := (3521259836533/1000000000000)
  V := (111644477/500000000000)
  mass := (36967/250000000000)
  rootN := (508392626487/500000000000)
  rootB := (5460417823/200000000000)
  rootU := (593975301611/1000000000000)
  rootV := (14942856287/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_42.scalar_checked
  centre := fun n hn => lowFull5_42 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy42 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_42.bound (by norm_num) hn lowTIParameters42_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_43 : FrameRectangleCertificate 11000 11882 (963/2000) (241/500) lowTIParameters43 where
  full := (1566679961/15625000000)
  energy := (697764510909/1000000000000)
  cov := (146264685327/500000000000)
  schur := (1034045440007/1000000000000)
  cap := (746056463/1000000000000)
  W2 := (3518241975423/1000000000000)
  V := (44704059/200000000000)
  mass := (137453/1000000000000)
  rootN := (1016880248607/1000000000000)
  rootB := (27314034177/1000000000000)
  rootU := (118788112007/200000000000)
  rootV := (14950595139/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_43.scalar_checked
  centre := fun n hn => lowFull5_43 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy43 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_43.bound (by norm_num) hn lowTIParameters43_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_44 : FrameRectangleCertificate 11000 11882 (241/500) (193/400) lowTIParameters44 where
  full := (100341727023/1000000000000)
  energy := (348761254081/500000000000)
  cov := (146416068193/500000000000)
  schur := (517119362693/500000000000)
  cap := (373354399/500000000000)
  W2 := (1757615343387/500000000000)
  V := (223751637/1000000000000)
  mass := (127887/1000000000000)
  rootN := (127121910323/125000000000)
  rootB := (27325972957/1000000000000)
  rootU := (593905984139/1000000000000)
  rootV := (14958330021/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_44.scalar_checked
  centre := fun n hn => lowFull5_44 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy44 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_44.bound (by norm_num) hn lowTIParameters44_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_45 : FrameRectangleCertificate 11000 11882 (193/400) (483/1000) lowTIParameters45 where
  full := (50207966543/500000000000)
  energy := (174320154681/250000000000)
  cov := (73283725583/250000000000)
  schur := (64652006653/62500000000)
  cap := (186840267/250000000000)
  W2 := (3512225949109/1000000000000)
  V := (223982979/1000000000000)
  mass := (14887/125000000000)
  rootN := (1017070354719/1000000000000)
  rootB := (13668952667/500000000000)
  rootU := (296935786783/500000000000)
  rootV := (2993212181/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_45.scalar_checked
  centre := fun n hn => lowFull5_45 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy45 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_45.bound (by norm_num) hn lowTIParameters45_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_46 : FrameRectangleCertificate 11000 11882 (483/1000) (967/2000) lowTIParameters46 where
  full := (100490135753/1000000000000)
  energy := (348519421259/500000000000)
  cov := (293437668497/1000000000000)
  schur := (1034625582907/1000000000000)
  cap := (748013281/1000000000000)
  W2 := (3509227741129/1000000000000)
  V := (224214321/1000000000000)
  mass := (13877/125000000000)
  rootN := (508582732431/500000000000)
  rootB := (27349831463/1000000000000)
  rootU := (296918663987/500000000000)
  rootV := (7486893899/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_46.scalar_checked
  centre := fun n hn => lowFull5_46 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy46 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_46.bound (by norm_num) hn lowTIParameters46_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_47 : FrameRectangleCertificate 11000 11882 (967/2000) (121/250) lowTIParameters47 where
  full := (2514108377/25000000000)
  energy := (87099647433/125000000000)
  cov := (146870217439/500000000000)
  schur := (1034819154441/1000000000000)
  cap := (74866543/100000000000)
  W2 := (876559010381/250000000000)
  V := (7013927/31250000000)
  mass := (51793/500000000000)
  rootN := (1017260612843/1000000000000)
  rootB := (3420218903/125000000000)
  rootU := (296901623501/500000000000)
  rootV := (14981510739/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_47.scalar_checked
  centre := fun n hn => lowFull5_47 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy47 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_47.bound (by norm_num) hn lowTIParameters47_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_48 : FrameRectangleCertificate 11000 11882 (121/250) (969/2000) lowTIParameters48 where
  full := (100638531127/1000000000000)
  energy := (348277814743/500000000000)
  cov := (147021600737/500000000000)
  schur := (258753205191/250000000000)
  cap := (749317519/1000000000000)
  W2 := (3503250829217/1000000000000)
  V := (112338503/500000000000)
  mass := (96753/1000000000000)
  rootN := (63584737407/62500000000)
  rootB := (27373664699/1000000000000)
  rootU := (118753866063/200000000000)
  rootV := (14989229667/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_48.scalar_checked
  centre := fun n hn => lowFull5_48 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy48 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_48.bound (by norm_num) hn lowTIParameters48_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_49 : FrameRectangleCertificate 11000 11882 (969/2000) (97/200) lowTIParameters49 where
  full := (25178180989/250000000000)
  energy := (348157096253/500000000000)
  cov := (9198311509/31250000000)
  schur := (1035206581577/1000000000000)
  cap := (374984773/500000000000)
  W2 := (1750136041571/500000000000)
  V := (224908349/1000000000000)
  mass := (45233/500000000000)
  rootN := (101745102171/100000000000)
  rootB := (27385571859/1000000000000)
  rootU := (593735577577/1000000000000)
  rootV := (937309041/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_49.scalar_checked
  centre := fun n hn => lowFull5_49 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy49 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_49.bound (by norm_num) hn lowTIParameters49_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_50 : FrameRectangleCertificate 11000 11882 (97/200) (971/2000) lowTIParameters50 where
  full := (806295309/8000000000)
  energy := (139214573689/200000000000)
  cov := (73662183829/250000000000)
  schur := (12942505457/12500000000)
  cap := (150124303/200000000000)
  W2 := (3497299782303/1000000000000)
  V := (56284923/250000000000)
  mass := (84681/1000000000000)
  rootN := (101754628227/100000000000)
  rootB := (5479494557/200000000000)
  rootU := (296850994221/500000000000)
  rootV := (7502327839/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_50.scalar_checked
  centre := fun n hn => lowFull5_50 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy50 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_50.bound (by norm_num) hn lowTIParameters50_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_51 : FrameRectangleCertificate 11000 11882 (971/2000) (243/500) lowTIParameters51 where
  full := (504305501/5000000000)
  energy := (695831657229/1000000000000)
  cov := (294951502559/1000000000000)
  schur := (1035594385437/1000000000000)
  cap := (751273423/1000000000000)
  W2 := (27954671247/8000000000)
  V := (45074207/200000000000)
  mass := (15871/200000000000)
  rootN := (508820790023/500000000000)
  rootB := (3426170929/125000000000)
  rootU := (118733712519/200000000000)
  rootV := (15012362739/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_51.scalar_checked
  centre := fun n hn => lowFull5_51 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy51 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_51.bound (by norm_num) hn lowTIParameters51_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_52 : FrameRectangleCertificate 11000 11882 (243/500) (973/2000) lowTIParameters52 where
  full := (100935283741/1000000000000)
  energy := (86948819847/125000000000)
  cov := (295254270017/1000000000000)
  schur := (103578842789/100000000000)
  cap := (751925271/1000000000000)
  W2 := (3491374433021/1000000000000)
  V := (112801189/500000000000)
  mass := (74451/1000000000000)
  rootN := (1017736914871/1000000000000)
  rootB := (1096850233/40000000000)
  rootU := (118727059939/200000000000)
  rootV := (7510032923/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_52.scalar_checked
  centre := fun n hn => lowFull5_52 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy52 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_52.bound (by norm_num) hn lowTIParameters52_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_53 : FrameRectangleCertificate 11000 11882 (973/2000) (487/1000) lowTIParameters53 where
  full := (10100946431/100000000000)
  energy := (69534957301/100000000000)
  cov := (295557037689/1000000000000)
  schur := (258995640909/250000000000)
  cap := (376288529/500000000000)
  W2 := (872105335769/250000000000)
  V := (225833721/1000000000000)
  mass := (69933/1000000000000)
  rootN := (254458071649/250000000000)
  rootB := (13716568977/500000000000)
  rootU := (593602199417/1000000000000)
  rootV := (3756941251/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_53.scalar_checked
  centre := fun n hn => lowFull5_53 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy53 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_53.bound (by norm_num) hn lowTIParameters53_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_54 : FrameRectangleCertificate 11000 11882 (487/1000) (39/80) lowTIParameters54 where
  full := (4043345679/40000000000)
  energy := (43444293741/62500000000)
  cov := (36982475697/125000000000)
  schur := (518088396193/500000000000)
  cap := (753228787/1000000000000)
  W2 := (1742737307731/500000000000)
  V := (45213013/200000000000)
  mass := (65771/1000000000000)
  rootN := (254481923767/250000000000)
  rootB := (27445013883/1000000000000)
  rootU := (296784630727/500000000000)
  rootV := (15035460253/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_54.scalar_checked
  centre := fun n hn => lowFull5_54 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy54 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_54.bound (by norm_num) hn lowTIParameters54_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_55 : FrameRectangleCertificate 11000 11882 (39/80) (61/125) lowTIParameters55 where
  full := (101157816799/1000000000000)
  energy := (694867939233/1000000000000)
  cov := (74040643419/250000000000)
  schur := (1036371113829/1000000000000)
  cap := (94235057/125000000000)
  W2 := (3482534229607/1000000000000)
  V := (28287051/125000000000)
  mass := (12387/200000000000)
  rootN := (8144185121/8000000000)
  rootB := (13728441791/500000000000)
  rootU := (14838412137/25000000000)
  rootV := (3760787883/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_55.scalar_checked
  centre := fun n hn => lowFull5_55 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy55 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_55.bound (by norm_num) hn lowTIParameters55_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_56 : FrameRectangleCertificate 11000 11882 (61/125) (977/2000) lowTIParameters56 where
  full := (101231988847/1000000000000)
  energy := (173656822767/250000000000)
  cov := (296465341987/1000000000000)
  schur := (1036565527683/1000000000000)
  cap := (150906413/200000000000)
  W2 := (3479600165131/1000000000000)
  V := (28315969/125000000000)
  mass := (58399/1000000000000)
  rootN := (1018118621617/1000000000000)
  rootB := (1373437353/50000000000)
  rootU := (593503871183/1000000000000)
  rootV := (7525419457/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_56.scalar_checked
  centre := fun n hn => lowFull5_56 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy56 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_56.bound (by norm_num) hn lowTIParameters56_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_57 : FrameRectangleCertificate 11000 11882 (977/2000) (489/1000) lowTIParameters57 where
  full := (50653079093/500000000000)
  energy := (8679834441/12500000000)
  cov := (296768110511/1000000000000)
  schur := (20735200673/20000000000)
  cap := (151036723/200000000000)
  W2 := (1738336200839/500000000000)
  V := (28344887/125000000000)
  mass := (27569/500000000000)
  rootN := (1018214139389/1000000000000)
  rootB := (13740302171/500000000000)
  rootU := (118694283651/200000000000)
  rootV := (3764630593/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_57.scalar_checked
  centre := fun n hn => lowFull5_57 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy57 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_57.bound (by norm_num) hn lowTIParameters57_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_58 : FrameRectangleCertificate 11000 11882 (489/1000) (979/2000) lowTIParameters58 where
  full := (50690162443/500000000000)
  energy := (694146331799/1000000000000)
  cov := (59414175849/200000000000)
  schur := (1036954631461/1000000000000)
  cap := (755835107/1000000000000)
  W2 := (173687545953/50000000000)
  V := (5674761/25000000000)
  mass := (52129/1000000000000)
  rootN := (1018309693297/1000000000000)
  rootB := (859139233/31250000000)
  rootU := (118687825281/200000000000)
  rootV := (15066201911/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_58.scalar_checked
  centre := fun n hn => lowFull5_58 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy58 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_58.bound (by norm_num) hn lowTIParameters58_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_59 : FrameRectangleCertificate 11000 11882 (979/2000) (49/100) lowTIParameters59 where
  full := (25363622253/250000000000)
  energy := (346953010271/500000000000)
  cov := (148686824097/500000000000)
  schur := (259287330207/250000000000)
  cap := (756486539/1000000000000)
  W2 := (3470835697057/1000000000000)
  V := (45444357/200000000000)
  mass := (24677/500000000000)
  rootN := (101840528319/100000000000)
  rootB := (27504300373/1000000000000)
  rootU := (148351748829/250000000000)
  rootV := (15073877571/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_59.scalar_checked
  centre := fun n hn => lowFull5_59 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy59 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_59.bound (by norm_num) hn lowTIParameters59_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_60 : FrameRectangleCertificate 11000 11882 (49/100) (981/2000) lowTIParameters60 where
  full := (101528650637/1000000000000)
  energy := (173416455359/250000000000)
  cov := (73770898759/250000000000)
  schur := (514158002367/500000000000)
  cap := (94082019/125000000000)
  W2 := (3467926715589/1000000000000)
  V := (112735983/500000000000)
  mass := (5849/125000000000)
  rootN := (507029586103/500000000000)
  rootB := (13717289747/500000000000)
  rootU := (9271484761/15625000000)
  rootV := (15015723959/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_60.scalar_checked
  centre := fun n hn => lowFull5_60 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy60 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_60.bound (by norm_num) hn lowTIParameters60_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_61 : FrameRectangleCertificate 11000 11882 (981/2000) (491/1000) lowTIParameters61 where
  full := (101602809827/1000000000000)
  energy := (346712867201/500000000000)
  cov := (73845929961/250000000000)
  schur := (1028509170937/1000000000000)
  cap := (753303271/1000000000000)
  W2 := (13535249823/3906250000)
  V := (22570129/100000000000)
  mass := (44427/1000000000000)
  rootN := (1014154411783/1000000000000)
  rootB := (27446370817/1000000000000)
  rootU := (118668642853/200000000000)
  rootV := (15023358147/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_61.scalar_checked
  centre := fun n hn => lowFull5_61 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy61 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_61.bound (by norm_num) hn lowTIParameters61_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_62 : FrameRectangleCertificate 11000 11882 (491/1000) (983/2000) lowTIParameters62 where
  full := (397175651/3906250000)
  energy := (693185759367/1000000000000)
  cov := (14784192243/50000000000)
  schur := (20574048541/20000000000)
  cap := (150790067/200000000000)
  W2 := (432765924311/125000000000)
  V := (112965307/500000000000)
  mass := (42243/1000000000000)
  rootN := (1014249686739/1000000000000)
  rootB := (1098326243/40000000000)
  rootU := (148327890931/250000000000)
  rootV := (7515494229/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_62.scalar_checked
  centre := fun n hn => lowFull5_62 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy62 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_62.bound (by norm_num) hn lowTIParameters62_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_63 : FrameRectangleCertificate 11000 11882 (983/2000) (123/250) lowTIParameters63 where
  full := (25437780299/250000000000)
  energy := (346472948127/500000000000)
  cov := (73995992521/250000000000)
  schur := (1028895772787/1000000000000)
  cap := (377298669/500000000000)
  W2 := (3459237015127/1000000000000)
  V := (113079969/500000000000)
  mass := (1609/40000000000)
  rootN := (507172498463/500000000000)
  rootB := (13734967583/500000000000)
  rootU := (74160009099/125000000000)
  rootV := (15038614897/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_63.scalar_checked
  centre := fun n hn => lowFull5_63 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy63 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_63.bound (by norm_num) hn lowTIParameters63_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_64 : FrameRectangleCertificate 11000 11882 (123/250) (197/400) lowTIParameters64 where
  full := (101825273517/1000000000000)
  energy := (346353072493/500000000000)
  cov := (74071023879/250000000000)
  schur := (1029089207867/1000000000000)
  cap := (188811071/250000000000)
  W2 := (3456352796887/1000000000000)
  V := (226389263/1000000000000)
  mass := (38361/1000000000000)
  rootN := (1014440342193/1000000000000)
  rootB := (6870427043/250000000000)
  rootU := (593248741183/1000000000000)
  rootV := (235097461/15625000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_64.scalar_checked
  centre := fun n hn => lowFull5_64 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy64 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_64.bound (by norm_num) hn lowTIParameters64_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_65 : FrameRectangleCertificate 11000 11882 (197/400) (493/1000) lowTIParameters65 where
  full := (50949711849/500000000000)
  energy := (346233252743/500000000000)
  cov := (59316844231/200000000000)
  schur := (128660341501/125000000000)
  cap := (30235647/40000000000)
  W2 := (1726737360047/500000000000)
  V := (226618587/1000000000000)
  mass := (36639/1000000000000)
  rootN := (126816965299/125000000000)
  rootB := (429585549/15625000000)
  rootU := (74152196079/125000000000)
  rootV := (15053856217/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_65.scalar_checked
  centre := fun n hn => lowFull5_65 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy65 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_65.bound (by norm_num) hn lowTIParameters65_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_66 : FrameRectangleCertificate 11000 11882 (493/1000) (987/2000) lowTIParameters66 where
  full := (101973571809/1000000000000)
  energy := (8652837221/12500000000)
  cov := (296884347/1000000000)
  schur := (64342271559/62500000000)
  cap := (756538007/1000000000000)
  W2 := (1725301382609/500000000000)
  V := (28355989/125000000000)
  mass := (17523/500000000000)
  rootN := (507315568691/500000000000)
  rootB := (27505235993/1000000000000)
  rootU := (296593277429/500000000000)
  rootV := (15061471111/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_66.scalar_checked
  centre := fun n hn => lowFull5_66 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy66 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_66.bound (by norm_num) hn lowTIParameters66_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_67 : FrameRectangleCertificate 11000 11882 (987/2000) (247/500) lowTIParameters67 where
  full := (102047717927/1000000000000)
  energy := (691987561493/1000000000000)
  cov := (297184473049/1000000000000)
  schur := (205934009277/200000000000)
  cap := (757184781/1000000000000)
  W2 := (344773691277/100000000000)
  V := (227077237/1000000000000)
  mass := (33573/1000000000000)
  rootN := (1014726587011/1000000000000)
  rootB := (2751699077/100000000000)
  rootU := (118631139919/200000000000)
  rootV := (3767270539/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_67.scalar_checked
  centre := fun n hn => lowFull5_67 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy67 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_67.bound (by norm_num) hn lowTIParameters67_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_68 : FrameRectangleCertificate 11000 11882 (247/500) (989/2000) lowTIParameters68 where
  full := (10212186213/100000000000)
  energy := (691748256849/1000000000000)
  cov := (148742299653/500000000000)
  schur := (514931918047/500000000000)
  cap := (757831499/1000000000000)
  W2 := (3444877143383/1000000000000)
  V := (113653281/500000000000)
  mass := (32211/1000000000000)
  rootN := (1014822071151/1000000000000)
  rootB := (2752873951/100000000000)
  rootU := (118625000517/200000000000)
  rootV := (15076689359/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_68.scalar_checked
  centre := fun n hn => lowFull5_68 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy68 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_68.bound (by norm_num) hn lowTIParameters68_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_69 : FrameRectangleCertificate 11000 11882 (989/2000) (99/200) lowTIParameters69 where
  full := (20439200899/200000000000)
  energy := (691509063673/1000000000000)
  cov := (37223090721/125000000000)
  schur := (515028856889/500000000000)
  cap := (758478161/1000000000000)
  W2 := (1721011718857/500000000000)
  V := (227535887/1000000000000)
  mass := (30951/1000000000000)
  rootN := (1014917589649/1000000000000)
  rootB := (13770241111/500000000000)
  rootU := (296547231783/500000000000)
  rootV := (603371709/40000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_69.scalar_checked
  centre := fun n hn => lowFull5_69 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy69 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_69.bound (by norm_num) hn lowTIParameters69_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_70 : FrameRectangleCertificate 11000 11882 (99/200) (991/2000) lowTIParameters70 where
  full := (1022701451/10000000000)
  energy := (691269981889/1000000000000)
  cov := (298084852433/1000000000000)
  schur := (64390729947/62500000000)
  cap := (379562383/500000000000)
  W2 := (3439175776519/1000000000000)
  V := (56941303/250000000000)
  mass := (3723/125000000000)
  rootN := (203002628471/200000000000)
  rootB := (5510443779/200000000000)
  rootU := (593064082279/1000000000000)
  rootV := (15091892261/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_70.scalar_checked
  centre := fun n hn => lowFull5_70 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy70 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_70.bound (by norm_num) hn lowTIParameters70_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_71 : FrameRectangleCertificate 11000 11882 (991/2000) (62/125) lowTIParameters71 where
  full := (102344284027/1000000000000)
  energy := (345515505711/500000000000)
  cov := (37298122413/125000000000)
  schur := (515222865991/500000000000)
  cap := (151954263/200000000000)
  W2 := (687266828139/200000000000)
  V := (113997269/500000000000)
  mass := (5741/200000000000)
  rootN := (1015108729143/1000000000000)
  rootB := (13781974777/500000000000)
  rootU := (593033858483/1000000000000)
  rootV := (3019897601/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_71.scalar_checked
  centre := fun n hn => lowFull5_71 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy71 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_71.bound (by norm_num) hn lowTIParameters71_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_72 : FrameRectangleCertificate 11000 11882 (62/125) (993/2000) lowTIParameters72 where
  full := (51209210677/500000000000)
  energy := (345396076099/500000000000)
  cov := (149342553189/500000000000)
  schur := (1030639871971/1000000000000)
  cap := (760417809/1000000000000)
  W2 := (3433498511141/1000000000000)
  V := (28527983/125000000000)
  mass := (5541/200000000000)
  rootN := (1015204349859/1000000000000)
  rootB := (13787837113/500000000000)
  rootU := (593003791921/1000000000000)
  rootV := (1510707993/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_72.scalar_checked
  centre := fun n hn => lowFull5_72 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy72 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_72.bound (by norm_num) hn lowTIParameters72_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_73 : FrameRectangleCertificate 11000 11882 (993/2000) (497/1000) lowTIParameters73 where
  full := (20498511433/200000000000)
  energy := (690553404141/1000000000000)
  cov := (149492616827/500000000000)
  schur := (515417049433/500000000000)
  cap := (152212849/200000000000)
  W2 := (1715334434437/500000000000)
  V := (228453189/1000000000000)
  mass := (26779/1000000000000)
  rootN := (1015300004367/1000000000000)
  rootB := (862106027/31250000000)
  rootU := (592973882357/1000000000000)
  rootV := (15114668009/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_73.scalar_checked
  centre := fun n hn => lowFull5_73 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy73 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_73.bound (by norm_num) hn lowTIParameters73_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_74 : FrameRectangleCertificate 11000 11882 (497/1000) (199/400) lowTIParameters74 where
  full := (102566691541/1000000000000)
  energy := (690314767177/1000000000000)
  cov := (59857072227/200000000000)
  schur := (128878551551/125000000000)
  cap := (380855313/500000000000)
  W2 := (3427845194993/1000000000000)
  V := (45736503/200000000000)
  mass := (25921/1000000000000)
  rootN := (101539569253/100000000000)
  rootB := (27599105529/1000000000000)
  rootU := (148236032387/250000000000)
  rootV := (15122252313/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_74.scalar_checked
  centre := fun n hn => lowFull5_74 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy74 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_74.bound (by norm_num) hn lowTIParameters74_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_75 : FrameRectangleCertificate 11000 11882 (199/400) (249/500) lowTIParameters75 where
  full := (102640824567/1000000000000)
  energy := (690076241231/1000000000000)
  cov := (299585488817/1000000000000)
  schur := (1031222812319/1000000000000)
  cap := (762356953/1000000000000)
  W2 := (3425027470673/1000000000000)
  V := (114455921/500000000000)
  mass := (25127/1000000000000)
  rootN := (1015491414203/1000000000000)
  rootB := (27610812249/1000000000000)
  rootU := (37057158329/62500000000)
  rootV := (945614553/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_75.scalar_checked
  centre := fun n hn => lowFull5_75 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy75 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_75.bound (by norm_num) hn lowTIParameters75_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_76 : FrameRectangleCertificate 11000 11882 (249/500) (997/2000) lowTIParameters76 where
  full := (12839369541/125000000000)
  energy := (172459456557/250000000000)
  cov := (299885616701/1000000000000)
  schur := (51570864917/50000000000)
  cap := (763003223/1000000000000)
  W2 := (3422215677151/1000000000000)
  V := (14321323/62500000000)
  mass := (2439/100000000000)
  rootN := (31737099039/31250000000)
  rootB := (1104900519/40000000000)
  rootU := (74110636659/125000000000)
  rootV := (7568704777/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_76.scalar_checked
  centre := fun n hn => lowFull5_76 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy76 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_76.bound (by norm_num) hn lowTIParameters76_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_77 : FrameRectangleCertificate 11000 11882 (997/2000) (499/1000) lowTIParameters77 where
  full := (102789086909/1000000000000)
  energy := (344799761047/500000000000)
  cov := (150092872393/500000000000)
  schur := (1031611870219/1000000000000)
  cap := (763649437/1000000000000)
  W2 := (170970489789/50000000000)
  V := (114685247/500000000000)
  mass := (23707/1000000000000)
  rootN := (253920739383/250000000000)
  rootB := (27634207733/1000000000000)
  rootU := (592855809347/1000000000000)
  rootV := (1514498247/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_77.scalar_checked
  centre := fun n hn => lowFull5_77 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy77 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_77.bound (by norm_num) hn lowTIParameters77_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_78 : FrameRectangleCertificate 11000 11882 (499/1000) (999/2000) lowTIParameters78 where
  full := (102863216399/1000000000000)
  energy := (344680664379/500000000000)
  cov := (300485873071/1000000000000)
  schur := (1031806527701/1000000000000)
  cap := (764295597/1000000000000)
  W2 := (341660980801/100000000000)
  V := (229599821/1000000000000)
  mass := (11537/500000000000)
  rootN := (1015778778919/1000000000000)
  rootB := (3455737071/125000000000)
  rootU := (148206670319/250000000000)
  rootV := (7576275817/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_78.scalar_checked
  centre := fun n hn => lowFull5_78 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy78 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_78.bound (by norm_num) hn lowTIParameters78_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_79 : FrameRectangleCertificate 11000 11882 (999/2000) (1/2) lowTIParameters79 where
  full := (20587468977/200000000000)
  energy := (689123246139/1000000000000)
  cov := (150393000779/500000000000)
  schur := (516000635257/500000000000)
  cap := (764941703/1000000000000)
  W2 := (853453923813/250000000000)
  V := (57457287/250000000000)
  mass := (11243/500000000000)
  rootN := (1015874633267/1000000000000)
  rootB := (13828789743/500000000000)
  rootU := (18524928401/31250000000)
  rootV := (15160117019/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_79.scalar_checked
  centre := fun n hn => lowFull5_79 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy79 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_79.bound (by norm_num) hn lowTIParameters79_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_80 : FrameRectangleCertificate 11000 11882 (1/2) (1001/2000) lowTIParameters80 where
  full := (12876434057/125000000000)
  energy := (688885274171/1000000000000)
  cov := (298473861581/1000000000000)
  schur := (1023248319543/1000000000000)
  cap := (761077273/1000000000000)
  W2 := (3411027439151/1000000000000)
  V := (228062453/1000000000000)
  mass := (21941/1000000000000)
  rootN := (1011557373333/1000000000000)
  rootB := (5517525797/200000000000)
  rootU := (18524027869/31250000000)
  rootV := (3020347351/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_80.scalar_checked
  centre := fun n hn => lowFull5_80 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy80 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_80.bound (by norm_num) hn lowTIParameters80_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_81 : FrameRectangleCertificate 11000 11882 (1001/2000) (501/1000) lowTIParameters81 where
  full := (20617119841/200000000000)
  energy := (68864741277/100000000000)
  cov := (298771379303/1000000000000)
  schur := (40937661331/40000000000)
  cap := (380859567/500000000000)
  W2 := (3408245021231/1000000000000)
  V := (28536223/125000000000)
  mass := (4287/200000000000)
  rootN := (505826435963/500000000000)
  rootB := (1724953729/62500000000)
  rootU := (592740229993/1000000000000)
  rootV := (15109261531/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_81.scalar_checked
  centre := fun n hn => lowFull5_81 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy81 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_81.bound (by norm_num) hn lowTIParameters81_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_82 : FrameRectangleCertificate 11000 11882 (501/1000) (1003/2000) lowTIParameters82 where
  full := (5157986261/50000000000)
  energy := (688409661873/1000000000000)
  cov := (299068897221/1000000000000)
  schur := (511817415433/500000000000)
  cap := (38118047/50000000000)
  W2 := (851367105847/250000000000)
  V := (57129279/250000000000)
  mass := (10483/500000000000)
  rootN := (252937100737/250000000000)
  rootB := (862840139/31250000000)
  rootU := (296355861593/500000000000)
  rootV := (3023356519/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_82.scalar_checked
  centre := fun n hn => lowFull5_82 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy82 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_82.bound (by norm_num) hn lowTIParameters82_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_83 : FrameRectangleCertificate 11000 11882 (1003/2000) (251/500) lowTIParameters83 where
  full := (103233850597/1000000000000)
  energy := (3440860107/5000000000)
  cov := (299366415337/1000000000000)
  schur := (1023828212021/1000000000000)
  cap := (190750673/250000000000)
  W2 := (42533720341/12500000000)
  V := (228744449/1000000000000)
  mass := (2053/100000000000)
  rootN := (1011843966243/1000000000000)
  rootB := (27622503363/1000000000000)
  rootU := (592683371187/1000000000000)
  rootV := (15124299951/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_83.scalar_checked
  centre := fun n hn => lowFull5_83 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy83 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_83.bound (by norm_num) hn lowTIParameters83_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_84 : FrameRectangleCertificate 11000 11882 (251/500) (201/400) lowTIParameters84 where
  full := (10330797543/100000000000)
  energy := (687934491279/1000000000000)
  cov := (299663933649/1000000000000)
  schur := (1024021676519/1000000000000)
  cap := (763644393/1000000000000)
  W2 := (679986522971/200000000000)
  V := (228971781/1000000000000)
  mass := (161/8000000000)
  rootN := (1011939561693/1000000000000)
  rootB := (27634116469/1000000000000)
  rootU := (592655173807/1000000000000)
  rootV := (756590677/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_84.scalar_checked
  centre := fun n hn => lowFull5_84 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy84 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_84.bound (by norm_num) hn lowTIParameters84_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_85 : FrameRectangleCertificate 11000 11882 (201/400) (503/1000) lowTIParameters85 where
  full := (25845524953/250000000000)
  energy := (171924267859/250000000000)
  cov := (149980726079/500000000000)
  schur := (512107612051/500000000000)
  cap := (764286039/1000000000000)
  W2 := (1698586684029/500000000000)
  V := (229199113/1000000000000)
  mass := (19749/1000000000000)
  rootN := (506017594581/500000000000)
  rootB := (13822861851/500000000000)
  rootU := (592627130847/1000000000000)
  rootV := (75696617/5000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_85.scalar_checked
  centre := fun n hn => lowFull5_85 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy85 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_85.bound (by norm_num) hn lowTIParameters85_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_86 : FrameRectangleCertificate 11000 11882 (503/1000) (1007/2000) lowTIParameters86 where
  full := (103456223841/1000000000000)
  energy := (3437298809/5000000000)
  cov := (15012948543/50000000000)
  schur := (256102213629/250000000000)
  cap := (764927633/1000000000000)
  W2 := (3394419868909/1000000000000)
  V := (114713223/500000000000)
  mass := (97/5000000000)
  rootN := (253032712129/250000000000)
  rootB := (6914331281/250000000000)
  rootU := (296299621063/500000000000)
  rootV := (1514682957/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_86.scalar_checked
  centre := fun n hn => lowFull5_86 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy86 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_86.bound (by norm_num) hn lowTIParameters86_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_87 : FrameRectangleCertificate 11000 11882 (1007/2000) (63/125) lowTIParameters87 where
  full := (20706069523/200000000000)
  energy := (137444512459/200000000000)
  cov := (150278244879/500000000000)
  schur := (1024602567527/1000000000000)
  cap := (765569173/1000000000000)
  W2 := (3391672099503/1000000000000)
  V := (229653779/1000000000000)
  mass := (763/40000000000)
  rootN := (253056634907/250000000000)
  rootB := (13834460353/500000000000)
  rootU := (74071438433/125000000000)
  rootV := (15154332021/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_87.scalar_checked
  centre := fun n hn => lowFull5_87 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy87 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_87.bound (by norm_num) hn lowTIParameters87_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_88 : FrameRectangleCertificate 11000 11882 (63/125) (1009/2000) lowTIParameters88 where
  full := (103604471233/1000000000000)
  energy := (686985472849/1000000000000)
  cov := (300854008853/1000000000000)
  schur := (1601244317/1562500000)
  cap := (766210661/1000000000000)
  W2 := (3388930042007/1000000000000)
  V := (28735139/125000000000)
  mass := (18773/1000000000000)
  rootN := (506161131183/500000000000)
  rootB := (27680510491/1000000000000)
  rootU := (592543926683/1000000000000)
  rootV := (15161830761/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_88.scalar_checked
  centre := fun n hn => lowFull5_88 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy88 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_88.bound (by norm_num) hn lowTIParameters88_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_89 : FrameRectangleCertificate 11000 11882 (1009/2000) (101/200) lowTIParameters89 where
  full := (51839297397/500000000000)
  energy := (686748493389/1000000000000)
  cov := (150575764069/500000000000)
  schur := (1024990240331/1000000000000)
  cap := (766852099/1000000000000)
  W2 := (3386193678721/1000000000000)
  V := (46021689/200000000000)
  mass := (18493/1000000000000)
  rootN := (506209008299/500000000000)
  rootB := (13846047261/500000000000)
  rootU := (592516499611/1000000000000)
  rootV := (15169325793/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_89.scalar_checked
  centre := fun n hn => lowFull5_89 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy89 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_89.bound (by norm_num) hn lowTIParameters89_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_90 : FrameRectangleCertificate 11000 11882 (101/200) (1011/2000) lowTIParameters90 where
  full := (103752718401/1000000000000)
  energy := (343255811921/500000000000)
  cov := (301449047621/1000000000000)
  schur := (512592099827/500000000000)
  cap := (767493483/1000000000000)
  W2 := (1691731495961/500000000000)
  V := (115167889/500000000000)
  mass := (2279/125000000000)
  rootN := (202502760441/200000000000)
  rootB := (5540734547/200000000000)
  rootU := (592489226081/1000000000000)
  rootV := (3794204281/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_90.scalar_checked
  centre := fun n hn => lowFull5_90 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy90 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_90.bound (by norm_num) hn lowTIParameters90_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_91 : FrameRectangleCertificate 11000 11882 (1011/2000) (253/500) lowTIParameters91 where
  full := (25956710539/250000000000)
  energy := (137254972827/200000000000)
  cov := (150873283647/500000000000)
  schur := (41015129623/40000000000)
  cap := (384067407/500000000000)
  W2 := (211296122751/62500000000)
  V := (230563111/1000000000000)
  mass := (17989/1000000000000)
  rootN := (506304809521/500000000000)
  rootB := (5543049031/200000000000)
  rootU := (592462105929/1000000000000)
  rootV := (15184304759/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_91.scalar_checked
  centre := fun n hn => lowFull5_91 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy91 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_91.bound (by norm_num) hn lowTIParameters91_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_92 : FrameRectangleCertificate 11000 11882 (253/500) (1013/2000) lowTIParameters92 where
  full := (103900966163/1000000000000)
  energy := (343019107099/500000000000)
  cov := (7551102179/25000000000)
  schur := (1025572362889/1000000000000)
  cap := (24024253/31250000000)
  W2 := (168900928877/50000000000)
  V := (46158089/200000000000)
  mass := (17763/1000000000000)
  rootN := (1012705466999/1000000000000)
  rootB := (13863405931/500000000000)
  rootU := (592435139001/1000000000000)
  rootV := (15191788737/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_92.scalar_checked
  centre := fun n hn => lowFull5_92 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy92 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_92.bound (by norm_num) hn lowTIParameters92_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_93 : FrameRectangleCertificate 11000 11882 (1013/2000) (507/1000) lowTIParameters93 where
  full := (3249221579/31250000000)
  energy := (685801673953/1000000000000)
  cov := (302341607221/1000000000000)
  schur := (102576656633/100000000000)
  cap := (384708663/500000000000)
  W2 := (3375304814929/1000000000000)
  V := (115508889/500000000000)
  mass := (17553/1000000000000)
  rootN := (1012801345937/1000000000000)
  rootB := (3467296601/125000000000)
  rootU := (296204162569/500000000000)
  rootV := (3799817249/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_93.scalar_checked
  centre := fun n hn => lowFull5_93 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy93 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_93.bound (by norm_num) hn lowTIParameters93_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_94 : FrameRectangleCertificate 11000 11882 (507/1000) (203/400) lowTIParameters94 where
  full := (104049215359/1000000000000)
  energy := (171391310833/250000000000)
  cov := (302639127471/1000000000000)
  schur := (1025960850677/1000000000000)
  cap := (385029253/500000000000)
  W2 := (3372596658903/1000000000000)
  V := (28905639/125000000000)
  mass := (17357/1000000000000)
  rootN := (126612156967/125000000000)
  rootB := (6937482009/250000000000)
  rootU := (592381664201/1000000000000)
  rootV := (15206745609/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_94.scalar_checked
  centre := fun n hn => lowFull5_94 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy94 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_94.bound (by norm_num) hn lowTIParameters94_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_95 : FrameRectangleCertificate 11000 11882 (203/400) (127/250) lowTIParameters95 where
  full := (52061670381/500000000000)
  energy := (685328922263/1000000000000)
  cov := (151468323957/500000000000)
  schur := (102615521569/100000000000)
  cap := (385349817/500000000000)
  W2 := (842473523029/250000000000)
  V := (115736223/500000000000)
  mass := (687/40000000000)
  rootN := (1012993196271/1000000000000)
  rootB := (27761477519/1000000000000)
  rootU := (592355156039/1000000000000)
  rootV := (3803554637/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_95.scalar_checked
  centre := fun n hn => lowFull5_95 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy95 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_95.bound (by norm_num) hn lowTIParameters95_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_96 : FrameRectangleCertificate 11000 11882 (127/250) (1017/2000) lowTIParameters96 where
  full := (3256170839/31250000000)
  energy := (685092710671/1000000000000)
  cov := (75808542137/250000000000)
  schur := (1026349661123/1000000000000)
  cap := (96417589/125000000000)
  W2 := (3367197097313/1000000000000)
  V := (11584989/50000000000)
  mass := (3401/200000000000)
  rootN := (101308916741/100000000000)
  rootB := (13886510649/500000000000)
  rootU := (296164400257/500000000000)
  rootV := (7610843909/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_96.scalar_checked
  centre := fun n hn => lowFull5_96 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy96 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_96.bound (by norm_num) hn lowTIParameters96_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_97 : FrameRectangleCertificate 11000 11882 (1017/2000) (509/1000) lowTIParameters97 where
  full := (104271593727/1000000000000)
  energy := (342428304243/500000000000)
  cov := (75882922343/250000000000)
  schur := (1026544186747/1000000000000)
  cap := (38599087/50000000000)
  W2 := (3364505657331/1000000000000)
  V := (46385423/200000000000)
  mass := (16847/1000000000000)
  rootN := (1013185169033/1000000000000)
  rootB := (13892279691/500000000000)
  rootU := (592302597491/1000000000000)
  rootV := (15229153457/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_97.scalar_checked
  centre := fun n hn => lowFull5_97 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy97 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_97.bound (by norm_num) hn lowTIParameters97_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_98 : FrameRectangleCertificate 11000 11882 (509/1000) (1019/2000) lowTIParameters98 where
  full := (13043215189/125000000000)
  energy := (171155153909/250000000000)
  cov := (151914605193/500000000000)
  schur := (1026738792337/1000000000000)
  cap := (386311359/500000000000)
  W2 := (420227469389/125000000000)
  V := (232154449/1000000000000)
  mass := (167/10000000000)
  rootN := (1013281201019/1000000000000)
  rootB := (217156967/7812500000)
  rootU := (148069136711/250000000000)
  rootV := (7618307703/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_98.scalar_checked
  centre := fun n hn => lowFull5_98 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy98 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_98.bound (by norm_num) hn lowTIParameters98_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_99 : FrameRectangleCertificate 11000 11882 (1019/2000) (51/100) lowTIParameters99 where
  full := (104419850317/1000000000000)
  energy := (42774045753/62500000000)
  cov := (304126731591/1000000000000)
  schur := (1026933477659/1000000000000)
  cap := (193315911/250000000000)
  W2 := (839784843403/250000000000)
  V := (232381783/1000000000000)
  mass := (16563/1000000000000)
  rootN := (253344315811/250000000000)
  rootB := (27807618453/1000000000000)
  rootU := (4626958191/7812500000)
  rootV := (15244073701/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_99.scalar_checked
  centre := fun n hn => lowFull5_99 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy99 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_99.bound (by norm_num) hn lowTIParameters99_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_100 : FrameRectangleCertificate 11000 11882 (51/100) (1021/2000) lowTIParameters100 where
  full := (20898796051/200000000000)
  energy := (684148957649/1000000000000)
  cov := (75448201841/250000000000)
  schur := (254564439871/250000000000)
  cap := (384682861/500000000000)
  W2 := (3356464495819/1000000000000)
  V := (230598443/1000000000000)
  mass := (3287/200000000000)
  rootN := (504543793809/500000000000)
  rootB := (27737442601/1000000000000)
  rootU := (592224902173/1000000000000)
  rootV := (15185468153/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_100.scalar_checked
  centre := fun n hn => lowFull5_100 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy100 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_100.bound (by norm_num) hn lowTIParameters100_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_101 : FrameRectangleCertificate 11000 11882 (1021/2000) (511/1000) lowTIParameters101 where
  full := (52284055723/500000000000)
  energy := (683913292373/1000000000000)
  cov := (30208775013/100000000000)
  schur := (509225455783/500000000000)
  cap := (770002469/1000000000000)
  W2 := (3353795104959/1000000000000)
  V := (230823807/1000000000000)
  mass := (4079/250000000000)
  rootN := (504591644691/500000000000)
  rootB := (1387445917/50000000000)
  rootU := (296099653961/500000000000)
  rootV := (3798221681/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_101.scalar_checked
  centre := fun n hn => lowFull5_101 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy101 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_101.bound (by norm_num) hn lowTIParameters101_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_102 : FrameRectangleCertificate 11000 11882 (511/1000) (1023/2000) lowTIParameters102 where
  full := (52321122003/500000000000)
  energy := (683677736143/1000000000000)
  cov := (151191346543/500000000000)
  schur := (15916314719/15625000000)
  cap := (770639169/1000000000000)
  W2 := (3351131184157/1000000000000)
  V := (57762293/250000000000)
  mass := (3241/200000000000)
  rootN := (504639510447/500000000000)
  rootB := (3470048561/125000000000)
  rootU := (296086932787/500000000000)
  rootV := (3800075427/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_102.scalar_checked
  centre := fun n hn => lowFull5_102 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy102 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_102.bound (by norm_num) hn lowTIParameters102_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_103 : FrameRectangleCertificate 11000 11882 (1023/2000) (64/125) lowTIParameters103 where
  full := (20943275611/200000000000)
  energy := (683442288889/1000000000000)
  cov := (75669409057/250000000000)
  schur := (1018837450581/1000000000000)
  cap := (38563791/50000000000)
  W2 := (1674236358323/500000000000)
  V := (231274537/1000000000000)
  mass := (16101/1000000000000)
  rootN := (504687391011/500000000000)
  rootB := (13885926509/500000000000)
  rootU := (23685943001/40000000000)
  rootV := (3801928269/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_103.scalar_checked
  centre := fun n hn => lowFull5_103 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy103 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_103.bound (by norm_num) hn lowTIParameters103_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_104 : FrameRectangleCertificate 11000 11882 (64/125) (41/80) lowTIParameters104 where
  full := (20958102743/200000000000)
  energy := (683206950541/1000000000000)
  cov := (9467893111/31250000000)
  schur := (1019030837037/1000000000000)
  cap := (771912421/1000000000000)
  W2 := (167290984289/50000000000)
  V := (231499901/1000000000000)
  mass := (4001/250000000000)
  rootN := (504735286323/500000000000)
  rootB := (6945827979/250000000000)
  rootU := (296061718089/500000000000)
  rootV := (7607560401/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_104.scalar_checked
  centre := fun n hn => lowFull5_104 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy104 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_104.bound (by norm_num) hn lowTIParameters104_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_105 : FrameRectangleCertificate 11000 11882 (41/80) (513/1000) lowTIParameters105 where
  full := (26216162777/250000000000)
  energy := (341485860513/500000000000)
  cov := (151633761531/500000000000)
  schur := (25480607529/25000000000)
  cap := (772548977/1000000000000)
  W2 := (3343172074927/1000000000000)
  V := (115862633/500000000000)
  mass := (7957/500000000000)
  rootN := (504783196323/500000000000)
  rootB := (27794765281/1000000000000)
  rootU := (118419689787/200000000000)
  rootV := (3044504991/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_105.scalar_checked
  centre := fun n hn => lowFull5_105 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy105 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_105.bound (by norm_num) hn lowTIParameters105_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_106 : FrameRectangleCertificate 11000 11882 (513/1000) (1027/2000) lowTIParameters106 where
  full := (52469395179/500000000000)
  energy := (27309464011/40000000000)
  cov := (151781233379/500000000000)
  schur := (203883568551/200000000000)
  cap := (773185483/1000000000000)
  W2 := (3340529867597/1000000000000)
  V := (231950631/1000000000000)
  mass := (1583/100000000000)
  rootN := (1009662241919/1000000000000)
  rootB := (27806213029/1000000000000)
  rootU := (592073613211/1000000000000)
  rootV := (15229925509/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_106.scalar_checked
  centre := fun n hn => lowFull5_106 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy106 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_106.bound (by norm_num) hn lowTIParameters106_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_107 : FrameRectangleCertificate 11000 11882 (1027/2000) (257/500) lowTIParameters107 where
  full := (105012931591/1000000000000)
  energy := (136500317643/200000000000)
  cov := (303857410637/1000000000000)
  schur := (203922292313/200000000000)
  cap := (773821943/1000000000000)
  W2 := (3337893047253/1000000000000)
  V := (232175997/1000000000000)
  mass := (15751/1000000000000)
  rootN := (1009758120327/1000000000000)
  rootB := (695441381/25000000000)
  rootU := (118409785783/200000000000)
  rootV := (7618661251/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_107.scalar_checked
  centre := fun n hn => lowFull5_107 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy107 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_107.bound (by norm_num) hn lowTIParameters107_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_108 : FrameRectangleCertificate 11000 11882 (257/500) (1029/2000) lowTIParameters108 where
  full := (52543537467/500000000000)
  energy := (85283335597/125000000000)
  cov := (152076177351/500000000000)
  schur := (1019805157399/1000000000000)
  cap := (154891671/200000000000)
  W2 := (3335261597537/1000000000000)
  V := (116200681/500000000000)
  mass := (7839/500000000000)
  rootN := (126231753471/125000000000)
  rootB := (27829091883/1000000000000)
  rootU := (148006098993/250000000000)
  rootV := (476397371/31250000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_108.scalar_checked
  centre := fun n hn => lowFull5_108 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy108 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_108.bound (by norm_num) hn lowTIParameters108_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_109 : FrameRectangleCertificate 11000 11882 (1029/2000) (103/200) lowTIParameters109 where
  full := (105161220517/1000000000000)
  energy := (682031889889/1000000000000)
  cov := (76111824737/250000000000)
  schur := (203999786003/200000000000)
  cap := (775094721/1000000000000)
  W2 := (1666317751051/500000000000)
  V := (232626727/1000000000000)
  mass := (15609/1000000000000)
  rootN := (201989992823/200000000000)
  rootB := (13920261501/500000000000)
  rootU := (592000014307/1000000000000)
  rootV := (7626052829/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_109.scalar_checked
  centre := fun n hn => lowFull5_109 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy109 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_109.bound (by norm_num) hn lowTIParameters109_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_110 : FrameRectangleCertificate 11000 11882 (103/200) (1031/2000) lowTIParameters110 where
  full := (10523536847/100000000000)
  energy := (681797203479/1000000000000)
  cov := (304742243379/1000000000000)
  schur := (510096389599/500000000000)
  cap := (775731039/1000000000000)
  W2 := (3330014744631/1000000000000)
  V := (232852093/1000000000000)
  mass := (3109/200000000000)
  rootN := (252511482313/250000000000)
  rootB := (3481493571/125000000000)
  rootU := (73996972981/125000000000)
  rootV := (15259491899/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_110.scalar_checked
  centre := fun n hn => lowFull5_110 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy110 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_110.bound (by norm_num) hn lowTIParameters110_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_111 : FrameRectangleCertificate 11000 11882 (1031/2000) (129/250) lowTIParameters111 where
  full := (4212380757/40000000000)
  energy := (340781312741/500000000000)
  cov := (305037187991/1000000000000)
  schur := (510193352373/500000000000)
  cap := (48522957/62500000000)
  W2 := (3327399309019/1000000000000)
  V := (233077459/1000000000000)
  mass := (3097/200000000000)
  rootN := (3945866887/3906250000)
  rootB := (27863368641/1000000000000)
  rootU := (591951704537/1000000000000)
  rootV := (7633437283/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_111.scalar_checked
  centre := fun n hn => lowFull5_111 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy111 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_111.bound (by norm_num) hn lowTIParameters111_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_112 : FrameRectangleCertificate 11000 11882 (129/250) (1033/2000) lowTIParameters112 where
  full := (6586479501/62500000000)
  energy := (340664077911/500000000000)
  cov := (61066426557/200000000000)
  schur := (1020580706421/1000000000000)
  cap := (777003539/1000000000000)
  W2 := (1662394589511/500000000000)
  V := (9332113/40000000000)
  mass := (15429/1000000000000)
  rootN := (126279743181/125000000000)
  rootB := (2787478321/100000000000)
  rootU := (147981944077/250000000000)
  rootV := (3054850733/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_112.scalar_checked
  centre := fun n hn => lowFull5_112 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy112 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_112.bound (by norm_num) hn lowTIParameters112_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_113 : FrameRectangleCertificate 11000 11882 (1033/2000) (517/1000) lowTIParameters113 where
  full := (52728913939/500000000000)
  energy := (681093794431/1000000000000)
  cov := (477542309/1562500000)
  schur := (1020774784017/1000000000000)
  cap := (19440993/25000000000)
  W2 := (3322184338629/1000000000000)
  V := (233528191/1000000000000)
  mass := (15377/1000000000000)
  rootN := (101033399627/100000000000)
  rootB := (27886192283/1000000000000)
  rootU := (59190399911/100000000000)
  rootV := (38204073/2500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_113.scalar_checked
  centre := fun n hn => lowFull5_113 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy113 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_113.bound (by norm_num) hn lowTIParameters113_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_114 : FrameRectangleCertificate 11000 11882 (517/1000) (207/400) lowTIParameters114 where
  full := (105531986649/1000000000000)
  energy := (340429770619/500000000000)
  cov := (76480505729/250000000000)
  schur := (1020968937321/1000000000000)
  cap := (155655171/200000000000)
  W2 := (3319584771819/1000000000000)
  V := (233753557/1000000000000)
  mass := (479/31250000000)
  rootN := (31575939857/31250000000)
  rootB := (5579519173/200000000000)
  rootU := (591880372897/1000000000000)
  rootV := (7644500589/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_114.scalar_checked
  centre := fun n hn => lowFull5_114 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy114 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_114.bound (by norm_num) hn lowTIParameters114_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_115 : FrameRectangleCertificate 11000 11882 (207/400) (259/500) lowTIParameters115 where
  full := (105606148467/1000000000000)
  energy := (680625396173/1000000000000)
  cov := (306216968253/1000000000000)
  schur := (204232633223/200000000000)
  cap := (97363993/125000000000)
  W2 := (1658495231309/500000000000)
  V := (233978923/1000000000000)
  mass := (15283/1000000000000)
  rootN := (252631545699/250000000000)
  rootB := (27908993963/1000000000000)
  rootU := (591856897619/1000000000000)
  rootV := (7648184801/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_115.scalar_checked
  centre := fun n hn => lowFull5_115 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy115 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_115.bound (by norm_num) hn lowTIParameters115_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_116 : FrameRectangleCertificate 11000 11882 (259/500) (1037/2000) lowTIParameters116 where
  full := (52840156737/500000000000)
  energy := (680391359169/1000000000000)
  cov := (306511913769/1000000000000)
  schur := (510678735097/500000000000)
  cap := (77954799/100000000000)
  W2 := (1657200697611/500000000000)
  V := (23420429/100000000000)
  mass := (381/25000000000)
  rootN := (40424892731/40000000000)
  rootB := (13960193319/500000000000)
  rootU := (2367334293/4000000000)
  rootV := (956483407/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_116.scalar_checked
  centre := fun n hn => lowFull5_116 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy116 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_116.bound (by norm_num) hn lowTIParameters116_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_117 : FrameRectangleCertificate 11000 11882 (1037/2000) (519/1000) lowTIParameters117 where
  full := (26438620453/250000000000)
  energy := (13603148603/20000000000)
  cov := (61361371893/200000000000)
  schur := (102155184933/100000000000)
  cap := (78018399/100000000000)
  W2 := (3311817553713/1000000000000)
  V := (29303707/125000000000)
  mass := (19/1250000000)
  rootN := (50535924087/50000000000)
  rootB := (27931773843/1000000000000)
  rootU := (147952599937/250000000000)
  rootV := (7655547923/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_117.scalar_checked
  centre := fun n hn => lowFull5_117 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy117 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_117.bound (by norm_num) hn lowTIParameters117_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_118 : FrameRectangleCertificate 11000 11882 (519/1000) (1039/2000) lowTIParameters118 where
  full := (13228581703/125000000000)
  energy := (169980902263/250000000000)
  cov := (15355090267/50000000000)
  schur := (1021746303331/1000000000000)
  cap := (195204987/250000000000)
  W2 := (1654619461217/500000000000)
  V := (234655023/1000000000000)
  mass := (15163/1000000000000)
  rootN := (1010814673089/1000000000000)
  rootB := (3492894457/125000000000)
  rootU := (591787377089/1000000000000)
  rootV := (3829613419/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_118.scalar_checked
  centre := fun n hn => lowFull5_118 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy118 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_118.bound (by norm_num) hn lowTIParameters118_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_119 : FrameRectangleCertificate 11000 11882 (1039/2000) (13/25) lowTIParameters119 where
  full := (105902829057/1000000000000)
  energy := (135937979161/200000000000)
  cov := (307396751393/1000000000000)
  schur := (1021940831981/1000000000000)
  cap := (781455861/1000000000000)
  W2 := (41333318571/12500000000)
  V := (23488039/100000000000)
  mass := (1891/125000000000)
  rootN := (1010910892207/1000000000000)
  rootB := (2795453203/100000000000)
  rootU := (118352901051/200000000000)
  rootV := (15325807973/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_119.scalar_checked
  centre := fun n hn => lowFull5_119 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy119 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_119.bound (by norm_num) hn lowTIParameters119_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_120 : FrameRectangleCertificate 11000 11882 (13/25) (1041/2000) lowTIParameters120 where
  full := (52988504129/500000000000)
  energy := (135891258067/200000000000)
  cov := (76260333681/250000000000)
  schur := (1013339388419/1000000000000)
  cap := (155504999/200000000000)
  W2 := (826024306949/250000000000)
  V := (233080627/1000000000000)
  mass := (3019/200000000000)
  rootN := (251661899731/250000000000)
  rootB := (5576827037/200000000000)
  rootU := (591741784223/1000000000000)
  rootV := (190837229/12500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_120.scalar_checked
  centre := fun n hn => lowFull5_120 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy120 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_120.bound (by norm_num) hn lowTIParameters120_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_121 : FrameRectangleCertificate 11000 11882 (1041/2000) (521/1000) lowTIParameters121 where
  full := (53025595689/500000000000)
  energy := (5306428067/7812500000)
  cov := (305333733679/1000000000000)
  schur := (506766190611/500000000000)
  cap := (155631359/200000000000)
  W2 := (3301534133237/1000000000000)
  V := (14581503/62500000000)
  mass := (1883/125000000000)
  rootN := (1006743453529/1000000000000)
  rootB := (27895461907/1000000000000)
  rootU := (59171921399/100000000000)
  rootV := (15274293699/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_121.scalar_checked
  centre := fun n hn => lowFull5_121 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy121 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_121.bound (by norm_num) hn lowTIParameters121_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_122 : FrameRectangleCertificate 11000 11882 (521/1000) (1043/2000) lowTIParameters122 where
  full := (106125378567/1000000000000)
  energy := (339494701229/500000000000)
  cov := (305626132809/1000000000000)
  schur := (253431361851/250000000000)
  cap := (15575771/20000000000)
  W2 := (824744046627/250000000000)
  V := (233527469/1000000000000)
  mass := (3759/250000000000)
  rootN := (125854916931/125000000000)
  rootB := (13953391613/500000000000)
  rootU := (591696794547/1000000000000)
  rootV := (15281605577/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_122.scalar_checked
  centre := fun n hn => lowFull5_122 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy122 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_122.bound (by norm_num) hn lowTIParameters122_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_123 : FrameRectangleCertificate 11000 11882 (1043/2000) (261/500) lowTIParameters123 where
  full := (53099784989/500000000000)
  energy := (84844514989/125000000000)
  cov := (305918532117/1000000000000)
  schur := (1013918586781/1000000000000)
  cap := (389710131/500000000000)
  W2 := (329642337217/100000000000)
  V := (23375089/100000000000)
  mass := (15009/1000000000000)
  rootN := (503467622291/500000000000)
  rootB := (1744881199/62500000000)
  rootU := (591674525893/1000000000000)
  rootV := (7644456979/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_123.scalar_checked
  centre := fun n hn => lowFull5_123 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy123 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_123.bound (by norm_num) hn lowTIParameters123_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_124 : FrameRectangleCertificate 11000 11882 (261/500) (209/400) lowTIParameters124 where
  full := (106273765769/1000000000000)
  energy := (678522944871/1000000000000)
  cov := (306210931597/1000000000000)
  schur := (50705589957/50000000000)
  cap := (390025967/500000000000)
  W2 := (411734459363/125000000000)
  V := (233974311/1000000000000)
  mass := (1873/125000000000)
  rootN := (1007031180819/1000000000000)
  rootB := (349117623/12500000000)
  rootU := (591652408047/1000000000000)
  rootV := (15296218847/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_124.scalar_checked
  centre := fun n hn => lowFull5_124 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy124 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_124.bound (by norm_num) hn lowTIParameters124_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_125 : FrameRectangleCertificate 11000 11882 (209/400) (523/1000) lowTIParameters125 where
  full := (53173983047/500000000000)
  energy := (33914493863/50000000000)
  cov := (49040533/160000000)
  schur := (1014305084251/1000000000000)
  cap := (780683563/1000000000000)
  W2 := (658266615861/200000000000)
  V := (58549433/250000000000)
  mass := (187/12500000000)
  rootN := (201425428807/200000000000)
  rootB := (27940715149/1000000000000)
  rootU := (147907610251/250000000000)
  rootV := (15303520249/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_125.scalar_checked
  centre := fun n hn => lowFull5_125 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy125 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_125.bound (by norm_num) hn lowTIParameters125_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_126 : FrameRectangleCertificate 11000 11882 (523/1000) (1047/2000) lowTIParameters126 where
  full := (13302771389/125000000000)
  energy := (84757114627/125000000000)
  cov := (7669893277/25000000000)
  schur := (507249220981/500000000000)
  cap := (781315151/1000000000000)
  W2 := (3288795570193/1000000000000)
  V := (234421153/1000000000000)
  mass := (7469/500000000000)
  rootN := (251805783537/250000000000)
  rootB := (27952015151/1000000000000)
  rootU := (147902156197/250000000000)
  rootV := (15310818169/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_126.scalar_checked
  centre := fun n hn => lowFull5_126 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy126 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_126.bound (by norm_num) hn lowTIParameters126_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_127 : FrameRectangleCertificate 11000 11882 (1047/2000) (131/250) lowTIParameters127 where
  full := (106496380987/1000000000000)
  energy := (169456016017/250000000000)
  cov := (7677203277/25000000000)
  schur := (1014691872029/1000000000000)
  cap := (781946697/1000000000000)
  W2 := (821565783089/250000000000)
  V := (9385783/40000000000)
  mass := (14917/1000000000000)
  rootN := (1007319151029/1000000000000)
  rootB := (27963309837/1000000000000)
  rootU := (59158695943/100000000000)
  rootV := (3063622529/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_127.scalar_checked
  centre := fun n hn => lowFull5_127 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy127 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_127.bound (by norm_num) hn lowTIParameters127_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_128 : FrameRectangleCertificate 11000 11882 (131/250) (1049/2000) lowTIParameters128 where
  full := (53285297939/500000000000)
  energy := (338795659173/500000000000)
  cov := (153690265627/500000000000)
  schur := (507442687139/500000000000)
  cap := (195644551/250000000000)
  W2 := (1641867875331/500000000000)
  V := (58716999/250000000000)
  mass := (7449/500000000000)
  rootN := (125926899323/125000000000)
  rootB := (5594919853/200000000000)
  rootU := (295782722473/500000000000)
  rootV := (15325403617/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_128.scalar_checked
  centre := fun n hn => lowFull5_128 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy128 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_128.bound (by norm_num) hn lowTIParameters128_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_129 : FrameRectangleCertificate 11000 11882 (1049/2000) (21/40) lowTIParameters129 where
  full := (106644815953/1000000000000)
  energy := (338679339891/500000000000)
  cov := (153836465801/500000000000)
  schur := (126884868563/125000000000)
  cap := (783209669/1000000000000)
  W2 := (3281213410039/1000000000000)
  V := (117545709/500000000000)
  mass := (93/6250000000)
  rootN := (15742363511/15625000000)
  rootB := (6996470847/250000000000)
  rootU := (591544081381/1000000000000)
  rootV := (7666345577/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_129.scalar_checked
  centre := fun n hn => lowFull5_129 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy129 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_129.bound (by norm_num) hn lowTIParameters129_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_130 : FrameRectangleCertificate 11000 11882 (21/40) (1051/2000) lowTIParameters130 where
  full := (53359520689/500000000000)
  energy := (677126148311/1000000000000)
  cov := (7699133303/25000000000)
  schur := (1015272594517/1000000000000)
  cap := (156768219/200000000000)
  W2 := (409837011943/125000000000)
  V := (5882871/25000000000)
  mass := (14863/1000000000000)
  rootN := (503803680643/500000000000)
  rootB := (27997162267/1000000000000)
  rootU := (295761434389/500000000000)
  rootV := (15339975229/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_130.scalar_checked
  centre := fun n hn => lowFull5_130 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy130 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_130.bound (by norm_num) hn lowTIParameters130_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_131 : FrameRectangleCertificate 11000 11882 (1051/2000) (263/500) lowTIParameters131 where
  full := (106793272321/1000000000000)
  energy := (676893723859/1000000000000)
  cov := (308257732809/1000000000000)
  schur := (1015466312099/1000000000000)
  cap := (784472481/1000000000000)
  W2 := (655236758427/200000000000)
  V := (117769131/500000000000)
  mass := (14847/1000000000000)
  rootN := (201540696843/200000000000)
  rootB := (2800843589/100000000000)
  rootU := (147875451793/250000000000)
  rootV := (7673627923/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_131.scalar_checked
  centre := fun n hn => lowFull5_131 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy131 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_131.bound (by norm_num) hn lowTIParameters131_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_132 : FrameRectangleCertificate 11000 11882 (263/500) (1053/2000) lowTIParameters132 where
  full := (106867508953/1000000000000)
  energy := (676661406363/1000000000000)
  cov := (308550133669/1000000000000)
  schur := (101566010109/100000000000)
  cap := (392551913/500000000000)
  W2 := (3273676485023/1000000000000)
  V := (58940421/250000000000)
  mass := (927/62500000000)
  rootN := (201559926681/200000000000)
  rootB := (14009852123/500000000000)
  rootU := (295740448313/500000000000)
  rootV := (3838633253/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_132.scalar_checked
  centre := fun n hn => lowFull5_132 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy132 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_132.bound (by norm_num) hn lowTIParameters132_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_133 : FrameRectangleCertificate 11000 11882 (1053/2000) (527/1000) lowTIParameters133 where
  full := (106941751449/1000000000000)
  energy := (84553649469/125000000000)
  cov := (3088425347/10000000000)
  schur := (1015853961259/1000000000000)
  cap := (785735133/1000000000000)
  W2 := (32711741593/10000000000)
  V := (117992553/500000000000)
  mass := (7409/500000000000)
  rootN := (251973952183/250000000000)
  rootB := (14015483697/500000000000)
  rootU := (118292027439/200000000000)
  rootV := (1536180673/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_133.scalar_checked
  centre := fun n hn => lowFull5_133 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy133 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_133.bound (by norm_num) hn lowTIParameters133_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_134 : FrameRectangleCertificate 11000 11882 (527/1000) (211/400) lowTIParameters134 where
  full := (6688499999/62500000000)
  energy := (16904927299/25000000000)
  cov := (309134935901/1000000000000)
  schur := (25401197311/25000000000)
  cap := (491479/625000000)
  W2 := (3268676800277/1000000000000)
  V := (14763033/62500000000)
  mass := (2961/200000000000)
  rootN := (251998002527/250000000000)
  rootB := (3505278163/125000000000)
  rootU := (73929941119/125000000000)
  rootV := (7684538503/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_134.scalar_checked
  centre := fun n hn => lowFull5_134 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy134 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_134.bound (by norm_num) hn lowTIParameters134_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_135 : FrameRectangleCertificate 11000 11882 (211/400) (66/125) lowTIParameters135 where
  full := (107090254733/1000000000000)
  energy := (135193018983/200000000000)
  cov := (309427337271/1000000000000)
  schur := (1016241894419/1000000000000)
  cap := (78699763/100000000000)
  W2 := (3266184393163/1000000000000)
  V := (236431951/1000000000000)
  mass := (1849/125000000000)
  rootN := (504044118709/500000000000)
  rootB := (14026739019/500000000000)
  rootU := (591419071953/1000000000000)
  rootV := (15376343877/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_135.scalar_checked
  centre := fun n hn => lowFull5_135 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy135 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_135.bound (by norm_num) hn lowTIParameters135_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_136 : FrameRectangleCertificate 11000 11882 (66/125) (1057/2000) lowTIParameters136 where
  full := (107164515877/1000000000000)
  energy := (84466650569/125000000000)
  cov := (309719738811/1000000000000)
  schur := (50821798351/50000000000)
  cap := (787628823/1000000000000)
  W2 := (65273938467/20000000000)
  V := (118327687/500000000000)
  mass := (14781/1000000000000)
  rootN := (126023061321/125000000000)
  rootB := (35080907/1250000000)
  rootU := (591398766283/1000000000000)
  rootV := (3076721463/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_136.scalar_checked
  centre := fun n hn => lowFull5_136 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy136 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_136.bound (by norm_num) hn lowTIParameters136_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_137 : FrameRectangleCertificate 11000 11882 (1057/2000) (529/1000) lowTIParameters137 where
  full := (107238783597/1000000000000)
  energy := (675501420803/1000000000000)
  cov := (7750303513/25000000000)
  schur := (25415752751/25000000000)
  cap := (98532497/125000000000)
  W2 := (407651797029/125000000000)
  V := (59219699/250000000000)
  mass := (1477/100000000000)
  rootN := (1008280769449/1000000000000)
  rootB := (5615193589/200000000000)
  rootU := (295689306011/500000000000)
  rootV := (15390867293/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_137.scalar_checked
  centre := fun n hn => lowFull5_137 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy137 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_137.bound (by norm_num) hn lowTIParameters137_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_138 : FrameRectangleCertificate 11000 11882 (529/1000) (1059/2000) lowTIParameters138 where
  full := (53656529039/500000000000)
  energy := (675269743601/1000000000000)
  cov := (310304542393/1000000000000)
  schur := (1016824323291/1000000000000)
  cap := (788891093/1000000000000)
  W2 := (1629368368657/500000000000)
  V := (237102219/1000000000000)
  mass := (14759/1000000000000)
  rootN := (504188536981/500000000000)
  rootB := (7021801287/250000000000)
  rootU := (295679304633/500000000000)
  rootV := (384953097/25000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_138.scalar_checked
  centre := fun n hn => lowFull5_138 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy138 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_138.bound (by norm_num) hn lowTIParameters138_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_139 : FrameRectangleCertificate 11000 11882 (1059/2000) (53/100) lowTIParameters139 where
  full := (21477467901/200000000000)
  energy := (168759543219/250000000000)
  cov := (77649236109/250000000000)
  schur := (50850930329/50000000000)
  cap := (789522171/1000000000000)
  W2 := (1628131996027/500000000000)
  V := (118662821/500000000000)
  mass := (59/4000000000)
  rootN := (1008473404003/1000000000000)
  rootB := (28098437163/1000000000000)
  rootU := (295669379051/500000000000)
  rootV := (15405377049/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_139.scalar_checked
  centre := fun n hn => lowFull5_139 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy139 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_139.bound (by norm_num) hn lowTIParameters139_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_140 : FrameRectangleCertificate 11000 11882 (53/100) (1061/2000) lowTIParameters140 where
  full := (53730814033/500000000000)
  energy := (134961341713/200000000000)
  cov := (308220320439/1000000000000)
  schur := (1008488651737/1000000000000)
  cap := (785558927/1000000000000)
  W2 := (406724515763/125000000000)
  V := (9420387/40000000000)
  mass := (14741/1000000000000)
  rootN := (502117678373/500000000000)
  rootB := (14013912079/500000000000)
  rootU := (147829764659/250000000000)
  rootV := (15346324479/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_140.scalar_checked
  centre := fun n hn => lowFull5_140 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy140 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_140.bound (by norm_num) hn lowTIParameters140_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_141 : FrameRectangleCertificate 11000 11882 (1061/2000) (531/1000) lowTIParameters141 where
  full := (107535923953/1000000000000)
  energy := (168643837649/250000000000)
  cov := (308510205781/1000000000000)
  schur := (504340698957/500000000000)
  cap := (786185959/1000000000000)
  W2 := (812833281263/250000000000)
  V := (9429247/40000000000)
  mass := (3683/250000000000)
  rootN := (251082829699/250000000000)
  rootB := (28039007811/1000000000000)
  rootU := (591299510977/1000000000000)
  rootV := (3070707899/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_141.scalar_checked
  centre := fun n hn => lowFull5_141 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy141 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_141.bound (by norm_num) hn lowTIParameters141_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_142 : FrameRectangleCertificate 11000 11882 (531/1000) (1063/2000) lowTIParameters142 where
  full := (107610227357/1000000000000)
  energy := (134868819781/200000000000)
  cov := (61760018257/200000000000)
  schur := (252218553243/250000000000)
  cap := (196703239/250000000000)
  W2 := (3248874974629/1000000000000)
  V := (9438107/40000000000)
  mass := (3681/250000000000)
  rootN := (1004427305967/1000000000000)
  rootB := (28050186381/1000000000000)
  rootU := (591280115237/1000000000000)
  rootV := (15360751121/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_142.scalar_checked
  centre := fun n hn => lowFull5_142 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy142 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_142.bound (by norm_num) hn lowTIParameters142_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_143 : FrameRectangleCertificate 11000 11882 (1063/2000) (133/250) lowTIParameters143 where
  full := (107684538473/1000000000000)
  energy := (674112953423/1000000000000)
  cov := (38636247119/125000000000)
  schur := (1009067096721/1000000000000)
  cap := (393719959/500000000000)
  W2 := (3246421660551/1000000000000)
  V := (7380443/31250000000)
  mass := (14717/1000000000000)
  rootN := (1004523318157/1000000000000)
  rootB := (224490879/8000000000)
  rootU := (591260871533/1000000000000)
  rootV := (15367959397/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_143.scalar_checked
  centre := fun n hn => lowFull5_143 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy143 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_143.bound (by norm_num) hn lowTIParameters143_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_144 : FrameRectangleCertificate 11000 11882 (133/250) (213/400) lowTIParameters144 where
  full := (107758857501/1000000000000)
  energy := (336940957041/500000000000)
  cov := (61875972557/200000000000)
  schur := (31539376531/31250000000)
  cap := (197016711/250000000000)
  W2 := (25951785349/8000000000)
  V := (59098919/250000000000)
  mass := (1471/100000000000)
  rootN := (40184774211/40000000000)
  rootB := (701813207/25000000000)
  rootU := (295620889999/500000000000)
  rootV := (768758213/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_144.scalar_checked
  centre := fun n hn => lowFull5_144 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy144 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_144.bound (by norm_num) hn lowTIParameters144_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_145 : FrameRectangleCertificate 11000 11882 (213/400) (533/1000) lowTIParameters145 where
  full := (107833184639/1000000000000)
  energy := (673650980819/1000000000000)
  cov := (15483487439/50000000000)
  schur := (504726534799/500000000000)
  cap := (157738747/200000000000)
  W2 := (12966117939/4000000000)
  V := (29577147/125000000000)
  mass := (14703/1000000000000)
  rootN := (50235770861/50000000000)
  rootB := (1404184581/50000000000)
  rootU := (118244568153/200000000000)
  rootV := (3845591437/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_145.scalar_checked
  centre := fun n hn => lowFull5_145 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy145 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_145.bound (by norm_num) hn lowTIParameters145_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_146 : FrameRectangleCertificate 11000 11882 (533/1000) (1067/2000) lowTIParameters146 where
  full := (107907520087/1000000000000)
  energy := (336710076781/500000000000)
  cov := (309959634939/1000000000000)
  schur := (1009646158349/1000000000000)
  cap := (49332537/62500000000)
  W2 := (3239090594789/1000000000000)
  V := (236838677/1000000000000)
  mass := (14697/1000000000000)
  rootN := (100481150389/100000000000)
  rootB := (43898203/1562500000)
  rootU := (295602026981/500000000000)
  rootV := (15389563899/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_146.scalar_checked
  centre := fun n hn => lowFull5_146 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy146 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_146.bound (by norm_num) hn lowTIParameters146_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_147 : FrameRectangleCertificate 11000 11882 (1067/2000) (267/500) lowTIParameters147 where
  full := (53990932027/500000000000)
  energy := (2692757729/4000000000)
  cov := (15512476063/50000000000)
  schur := (504919657543/500000000000)
  cap := (789947417/1000000000000)
  W2 := (3236656484801/1000000000000)
  V := (118530089/500000000000)
  mass := (14691/1000000000000)
  rootN := (1256134519/1250000000)
  rootB := (1405300161/50000000000)
  rootU := (147796354939/250000000000)
  rootV := (3079351737/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_147.scalar_checked
  centre := fun n hn => lowFull5_147 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy147 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_147.bound (by norm_num) hn lowTIParameters147_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_148 : FrameRectangleCertificate 11000 11882 (267/500) (1069/2000) lowTIParameters148 where
  full := (108056216743/1000000000000)
  energy := (168239704203/250000000000)
  cov := (310539407741/1000000000000)
  schur := (202006507921/200000000000)
  cap := (790574207/1000000000000)
  W2 := (404278392593/125000000000)
  V := (237281679/1000000000000)
  mass := (7343/500000000000)
  rootN := (1005003751041/1000000000000)
  rootB := (14058575737/500000000000)
  rootU := (591166938281/1000000000000)
  rootV := (15403950111/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_148.scalar_checked
  centre := fun n hn => lowFull5_148 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy148 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_148.bound (by norm_num) hn lowTIParameters148_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_149 : FrameRectangleCertificate 11000 11882 (1069/2000) (107/200) lowTIParameters149 where
  full := (54065289183/500000000000)
  energy := (336364153591/500000000000)
  cov := (310829294383/1000000000000)
  schur := (505112915863/500000000000)
  cap := (791200967/1000000000000)
  W2 := (646360509743/200000000000)
  V := (11875159/50000000000)
  mass := (367/25000000000)
  rootN := (251274977829/250000000000)
  rootB := (3516036847/125000000000)
  rootU := (295574304853/500000000000)
  rootV := (770556909/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_149.scalar_checked
  centre := fun n hn => lowFull5_149 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy149 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_149.bound (by norm_num) hn lowTIParameters149_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_150 : FrameRectangleCertificate 11000 11882 (107/200) (1071/2000) lowTIParameters150 where
  full := (54102474567/500000000000)
  energy := (10507779739/15625000000)
  cov := (311119181189/1000000000000)
  schur := (505209595651/500000000000)
  cap := (791827691/1000000000000)
  W2 := (1614691347433/500000000000)
  V := (237724681/1000000000000)
  mass := (587/40000000000)
  rootN := (201039219189/200000000000)
  rootB := (14069716513/500000000000)
  rootU := (147782608549/250000000000)
  rootV := (15418322899/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_150.scalar_checked
  centre := fun n hn => lowFull5_150 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy150 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_150.bound (by norm_num) hn lowTIParameters150_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_151 : FrameRectangleCertificate 11000 11882 (1071/2000) (67/125) lowTIParameters151 where
  full := (5413966463/50000000000)
  energy := (134453521017/200000000000)
  cov := (38926133519/125000000000)
  schur := (505306309061/500000000000)
  cap := (158490877/200000000000)
  W2 := (3226967565401/1000000000000)
  V := (118973091/500000000000)
  mass := (14671/1000000000000)
  rootN := (62830769051/62500000000)
  rootB := (439852599/15625000000)
  rootU := (7388905149/12500000000)
  rootV := (15425504271/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_151.scalar_checked
  centre := fun n hn => lowFull5_151 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy151 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_151.bound (by norm_num) hn lowTIParameters151_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_152 : FrameRectangleCertificate 11000 11882 (67/125) (1073/2000) lowTIParameters152 where
  full := (27088429741/250000000000)
  energy := (336018706243/500000000000)
  cov := (77924738819/250000000000)
  schur := (40432244481/40000000000)
  cap := (793081049/1000000000000)
  W2 := (3224557146563/1000000000000)
  V := (238167683/1000000000000)
  mass := (14667/1000000000000)
  rootN := (1005388537843/1000000000000)
  rootB := (3520211839/125000000000)
  rootU := (295547271533/500000000000)
  rootV := (15432682301/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_152.scalar_checked
  centre := fun n hn => lowFull5_152 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy152 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_152.bound (by norm_num) hn lowTIParameters152_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_153 : FrameRectangleCertificate 11000 11882 (1073/2000) (537/1000) lowTIParameters153 where
  full := (1694189351/15625000000)
  energy := (167951831357/250000000000)
  cov := (155994421279/500000000000)
  schur := (1010999672821/1000000000000)
  cap := (793707679/1000000000000)
  W2 := (3222151424611/1000000000000)
  V := (47677837/200000000000)
  mass := (7331/500000000000)
  rootN := (1005484794923/1000000000000)
  rootB := (3521602261/125000000000)
  rootU := (591076827813/1000000000000)
  rootV := (15439857027/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_153.scalar_checked
  centre := fun n hn => lowFull5_153 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy153 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_153.bound (by norm_num) hn lowTIParameters153_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_154 : FrameRectangleCertificate 11000 11882 (537/1000) (43/80) lowTIParameters154 where
  full := (5425126399/50000000000)
  energy := (13431546877/20000000000)
  cov := (312278730001/1000000000000)
  schur := (1011193300363/1000000000000)
  cap := (794334279/1000000000000)
  W2 := (3219750385961/1000000000000)
  V := (238610687/1000000000000)
  mass := (14659/1000000000000)
  rootN := (1005581075977/1000000000000)
  rootB := (14091968271/500000000000)
  rootU := (591059266353/1000000000000)
  rootV := (772351421/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_154.scalar_checked
  centre := fun n hn => lowFull5_154 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy154 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_154.bound (by norm_num) hn lowTIParameters154_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_155 : FrameRectangleCertificate 11000 11882 (43/80) (269/500) lowTIParameters155 where
  full := (108576947739/1000000000000)
  energy := (671347467681/1000000000000)
  cov := (97677693/312500000)
  schur := (25284674861/25000000000)
  cap := (794960849/1000000000000)
  W2 := (3217354016961/1000000000000)
  V := (59708047/250000000000)
  mass := (2931/200000000000)
  rootN := (502838690447/500000000000)
  rootB := (176219063/6250000000)
  rootU := (73880232361/125000000000)
  rootV := (15454196453/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_155.scalar_checked
  centre := fun n hn => lowFull5_155 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy155 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_155.bound (by norm_num) hn lowTIParameters155_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_156 : FrameRectangleCertificate 11000 11882 (269/500) (1077/2000) lowTIParameters156 where
  full := (6790711123/62500000000)
  energy := (33555884843/50000000000)
  cov := (312858505359/1000000000000)
  schur := (31611898591/31250000000)
  cap := (198896847/250000000000)
  W2 := (642992460823/200000000000)
  V := (23905369/100000000000)
  mass := (3663/250000000000)
  rootN := (201154741919/200000000000)
  rootB := (2820615869/100000000000)
  rootU := (147756151407/250000000000)
  rootV := (3092272239/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_156.scalar_checked
  centre := fun n hn => lowFull5_156 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy156 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_156.bound (by norm_num) hn lowTIParameters156_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_157 : FrameRectangleCertificate 11000 11882 (1077/2000) (539/1000) lowTIParameters157 where
  full := (108725818897/1000000000000)
  energy := (670888031319/1000000000000)
  cov := (12525935731/40000000000)
  schur := (1011774581597/1000000000000)
  cap := (398106949/500000000000)
  W2 := (3212575233943/1000000000000)
  V := (29909399/125000000000)
  mass := (1831/125000000000)
  rootN := (201174012397/200000000000)
  rootB := (7054315603/250000000000)
  rootU := (147751876697/250000000000)
  rootV := (15468522619/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_157.scalar_checked
  centre := fun n hn => lowFull5_157 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy157 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_157.bound (by norm_num) hn lowTIParameters157_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_158 : FrameRectangleCertificate 11000 11882 (539/1000) (1079/2000) lowTIParameters158 where
  full := (108800270757/1000000000000)
  energy := (670658470991/1000000000000)
  cov := (156719140673/500000000000)
  schur := (10119684743/10000000000)
  cap := (796840381/1000000000000)
  W2 := (401274099121/125000000000)
  V := (119748347/500000000000)
  mass := (2929/200000000000)
  rootN := (25149160949/25000000000)
  rootB := (3528545161/125000000000)
  rootU := (590990562579/1000000000000)
  rootV := (15475680729/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_158.scalar_checked
  centre := fun n hn => lowFull5_158 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy158 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_158.bound (by norm_num) hn lowTIParameters158_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle5_159 : FrameRectangleCertificate 11000 11882 (1079/2000) (27/50) lowTIParameters159 where
  full := (21774946757/200000000000)
  energy := (670429015813/1000000000000)
  cov := (12549126783/40000000000)
  schur := (506081216439/500000000000)
  cap := (797466833/1000000000000)
  W2 := (400976870979/125000000000)
  V := (59929549/250000000000)
  mass := (14643/1000000000000)
  rootN := (1006062837441/1000000000000)
  rootB := (14119727627/500000000000)
  rootU := (295486886619/500000000000)
  rootV := (15482835529/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness5_159.scalar_checked
  centre := fun n hn => lowFull5_159 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy159 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness5_159.bound (by norm_num) hn lowTIParameters159_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangles5 (j : Fin 160) :
    FrameRectangleCertificate 11000 11882 (frameNoiseLower j) (frameNoiseUpper j) (lowTIParameters j) := by
  match j with
  | ⟨0,_⟩ => convert lowRectangle5_0 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨1,_⟩ => convert lowRectangle5_1 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨2,_⟩ => convert lowRectangle5_2 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨3,_⟩ => convert lowRectangle5_3 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨4,_⟩ => convert lowRectangle5_4 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨5,_⟩ => convert lowRectangle5_5 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨6,_⟩ => convert lowRectangle5_6 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨7,_⟩ => convert lowRectangle5_7 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨8,_⟩ => convert lowRectangle5_8 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨9,_⟩ => convert lowRectangle5_9 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨10,_⟩ => convert lowRectangle5_10 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨11,_⟩ => convert lowRectangle5_11 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨12,_⟩ => convert lowRectangle5_12 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨13,_⟩ => convert lowRectangle5_13 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨14,_⟩ => convert lowRectangle5_14 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨15,_⟩ => convert lowRectangle5_15 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨16,_⟩ => convert lowRectangle5_16 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨17,_⟩ => convert lowRectangle5_17 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨18,_⟩ => convert lowRectangle5_18 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨19,_⟩ => convert lowRectangle5_19 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨20,_⟩ => convert lowRectangle5_20 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨21,_⟩ => convert lowRectangle5_21 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨22,_⟩ => convert lowRectangle5_22 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨23,_⟩ => convert lowRectangle5_23 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨24,_⟩ => convert lowRectangle5_24 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨25,_⟩ => convert lowRectangle5_25 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨26,_⟩ => convert lowRectangle5_26 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨27,_⟩ => convert lowRectangle5_27 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨28,_⟩ => convert lowRectangle5_28 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨29,_⟩ => convert lowRectangle5_29 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨30,_⟩ => convert lowRectangle5_30 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨31,_⟩ => convert lowRectangle5_31 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨32,_⟩ => convert lowRectangle5_32 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨33,_⟩ => convert lowRectangle5_33 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨34,_⟩ => convert lowRectangle5_34 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨35,_⟩ => convert lowRectangle5_35 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨36,_⟩ => convert lowRectangle5_36 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨37,_⟩ => convert lowRectangle5_37 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨38,_⟩ => convert lowRectangle5_38 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨39,_⟩ => convert lowRectangle5_39 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨40,_⟩ => convert lowRectangle5_40 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨41,_⟩ => convert lowRectangle5_41 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨42,_⟩ => convert lowRectangle5_42 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨43,_⟩ => convert lowRectangle5_43 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨44,_⟩ => convert lowRectangle5_44 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨45,_⟩ => convert lowRectangle5_45 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨46,_⟩ => convert lowRectangle5_46 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨47,_⟩ => convert lowRectangle5_47 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨48,_⟩ => convert lowRectangle5_48 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨49,_⟩ => convert lowRectangle5_49 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨50,_⟩ => convert lowRectangle5_50 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨51,_⟩ => convert lowRectangle5_51 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨52,_⟩ => convert lowRectangle5_52 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨53,_⟩ => convert lowRectangle5_53 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨54,_⟩ => convert lowRectangle5_54 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨55,_⟩ => convert lowRectangle5_55 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨56,_⟩ => convert lowRectangle5_56 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨57,_⟩ => convert lowRectangle5_57 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨58,_⟩ => convert lowRectangle5_58 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨59,_⟩ => convert lowRectangle5_59 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨60,_⟩ => convert lowRectangle5_60 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨61,_⟩ => convert lowRectangle5_61 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨62,_⟩ => convert lowRectangle5_62 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨63,_⟩ => convert lowRectangle5_63 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨64,_⟩ => convert lowRectangle5_64 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨65,_⟩ => convert lowRectangle5_65 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨66,_⟩ => convert lowRectangle5_66 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨67,_⟩ => convert lowRectangle5_67 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨68,_⟩ => convert lowRectangle5_68 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨69,_⟩ => convert lowRectangle5_69 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨70,_⟩ => convert lowRectangle5_70 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨71,_⟩ => convert lowRectangle5_71 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨72,_⟩ => convert lowRectangle5_72 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨73,_⟩ => convert lowRectangle5_73 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨74,_⟩ => convert lowRectangle5_74 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨75,_⟩ => convert lowRectangle5_75 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨76,_⟩ => convert lowRectangle5_76 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨77,_⟩ => convert lowRectangle5_77 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨78,_⟩ => convert lowRectangle5_78 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨79,_⟩ => convert lowRectangle5_79 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨80,_⟩ => convert lowRectangle5_80 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨81,_⟩ => convert lowRectangle5_81 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨82,_⟩ => convert lowRectangle5_82 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨83,_⟩ => convert lowRectangle5_83 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨84,_⟩ => convert lowRectangle5_84 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨85,_⟩ => convert lowRectangle5_85 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨86,_⟩ => convert lowRectangle5_86 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨87,_⟩ => convert lowRectangle5_87 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨88,_⟩ => convert lowRectangle5_88 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨89,_⟩ => convert lowRectangle5_89 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨90,_⟩ => convert lowRectangle5_90 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨91,_⟩ => convert lowRectangle5_91 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨92,_⟩ => convert lowRectangle5_92 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨93,_⟩ => convert lowRectangle5_93 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨94,_⟩ => convert lowRectangle5_94 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨95,_⟩ => convert lowRectangle5_95 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨96,_⟩ => convert lowRectangle5_96 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨97,_⟩ => convert lowRectangle5_97 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨98,_⟩ => convert lowRectangle5_98 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨99,_⟩ => convert lowRectangle5_99 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨100,_⟩ => convert lowRectangle5_100 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨101,_⟩ => convert lowRectangle5_101 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨102,_⟩ => convert lowRectangle5_102 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨103,_⟩ => convert lowRectangle5_103 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨104,_⟩ => convert lowRectangle5_104 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨105,_⟩ => convert lowRectangle5_105 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨106,_⟩ => convert lowRectangle5_106 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨107,_⟩ => convert lowRectangle5_107 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨108,_⟩ => convert lowRectangle5_108 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨109,_⟩ => convert lowRectangle5_109 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨110,_⟩ => convert lowRectangle5_110 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨111,_⟩ => convert lowRectangle5_111 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨112,_⟩ => convert lowRectangle5_112 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨113,_⟩ => convert lowRectangle5_113 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨114,_⟩ => convert lowRectangle5_114 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨115,_⟩ => convert lowRectangle5_115 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨116,_⟩ => convert lowRectangle5_116 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨117,_⟩ => convert lowRectangle5_117 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨118,_⟩ => convert lowRectangle5_118 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨119,_⟩ => convert lowRectangle5_119 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨120,_⟩ => convert lowRectangle5_120 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨121,_⟩ => convert lowRectangle5_121 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨122,_⟩ => convert lowRectangle5_122 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨123,_⟩ => convert lowRectangle5_123 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨124,_⟩ => convert lowRectangle5_124 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨125,_⟩ => convert lowRectangle5_125 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨126,_⟩ => convert lowRectangle5_126 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨127,_⟩ => convert lowRectangle5_127 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨128,_⟩ => convert lowRectangle5_128 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨129,_⟩ => convert lowRectangle5_129 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨130,_⟩ => convert lowRectangle5_130 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨131,_⟩ => convert lowRectangle5_131 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨132,_⟩ => convert lowRectangle5_132 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨133,_⟩ => convert lowRectangle5_133 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨134,_⟩ => convert lowRectangle5_134 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨135,_⟩ => convert lowRectangle5_135 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨136,_⟩ => convert lowRectangle5_136 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨137,_⟩ => convert lowRectangle5_137 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨138,_⟩ => convert lowRectangle5_138 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨139,_⟩ => convert lowRectangle5_139 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨140,_⟩ => convert lowRectangle5_140 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨141,_⟩ => convert lowRectangle5_141 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨142,_⟩ => convert lowRectangle5_142 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨143,_⟩ => convert lowRectangle5_143 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨144,_⟩ => convert lowRectangle5_144 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨145,_⟩ => convert lowRectangle5_145 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨146,_⟩ => convert lowRectangle5_146 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨147,_⟩ => convert lowRectangle5_147 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨148,_⟩ => convert lowRectangle5_148 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨149,_⟩ => convert lowRectangle5_149 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨150,_⟩ => convert lowRectangle5_150 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨151,_⟩ => convert lowRectangle5_151 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨152,_⟩ => convert lowRectangle5_152 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨153,_⟩ => convert lowRectangle5_153 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨154,_⟩ => convert lowRectangle5_154 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨155,_⟩ => convert lowRectangle5_155 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨156,_⟩ => convert lowRectangle5_156 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨157,_⟩ => convert lowRectangle5_157 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨158,_⟩ => convert lowRectangle5_158 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨159,_⟩ => convert lowRectangle5_159 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨j+160,h⟩ => exact False.elim (by omega)
end BstLean.BlueprintLow
