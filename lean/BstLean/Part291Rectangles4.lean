import BstLean.Part291Rectangle
import BstLean.Part291Certificates4
import BstLean.Part291LocalEnergyBatch0
import BstLean.Part291LocalEnergyBatch1
namespace BstLean.BlueprintLow
open Real Set BstLean.Part255
noncomputable def lowRectangle4_0 : FrameRectangleCertificate 10000 11000 (23/50) (921/2000) lowTIParameters0 where
  full := (98244178507/1000000000000)
  energy := (44267434443/62500000000)
  cov := (28448010839/100000000000)
  schur := (1045909270599/1000000000000)
  cap := (794731777/1000000000000)
  W2 := (1830106347571/500000000000)
  V := (119553441/500000000000)
  mass := (4354837/250000000000)
  rootN := (10226970571/10000000000)
  rootB := (14095493757/500000000000)
  rootU := (299831031331/500000000000)
  rootV := (15463081259/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_0.scalar_checked
  centre := fun n hn => lowFull4_0 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy0 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_0.bound (by norm_num) hn lowTIParameters0_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_1 : FrameRectangleCertificate 10000 11000 (921/2000) (461/1000) lowTIParameters1 where
  full := (98319035471/1000000000000)
  energy := (708032000171/1000000000000)
  cov := (284662392297/1000000000000)
  schur := (1045637798179/1000000000000)
  cap := (397609129/500000000000)
  W2 := (1828443187631/500000000000)
  V := (59815023/250000000000)
  mass := (1584399/100000000000)
  rootN := (204512864943/200000000000)
  rootB := (28199614501/1000000000000)
  rootU := (149904457331/250000000000)
  rootV := (15468034523/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_1.scalar_checked
  centre := fun n hn => lowFull4_1 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy1 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_1.bound (by norm_num) hn lowTIParameters1_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_2 : FrameRectangleCertificate 10000 11000 (461/1000) (923/2000) lowTIParameters2 where
  full := (98393893113/1000000000000)
  energy := (353892583027/500000000000)
  cov := (71211122083/250000000000)
  schur := (261341646181/250000000000)
  cap := (795704353/1000000000000)
  W2 := (730713531509/200000000000)
  V := (47882629/200000000000)
  mass := (2883867/200000000000)
  rootN := (1022431701741/1000000000000)
  rootB := (3526029001/125000000000)
  rootU := (599573803279/1000000000000)
  rootV := (15472981129/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_2.scalar_checked
  centre := fun n hn => lowFull4_2 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy2 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_2.bound (by norm_num) hn lowTIParameters2_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_3 : FrameRectangleCertificate 10000 11000 (923/2000) (231/500) lowTIParameters3 where
  full := (24617187893/250000000000)
  energy := (707538448651/1000000000000)
  cov := (285152375571/1000000000000)
  schur := (1045557235537/1000000000000)
  cap := (199107091/250000000000)
  W2 := (912564128971/250000000000)
  V := (9586877/40000000000)
  mass := (3282603/250000000000)
  rootN := (1022524931499/1000000000000)
  rootB := (14110531209/500000000000)
  rootU := (599529984269/1000000000000)
  rootV := (15481341189/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_3.scalar_checked
  centre := fun n hn => lowFull4_3 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy3 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_3.bound (by norm_num) hn lowTIParameters3_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_4 : FrameRectangleCertificate 10000 11000 (231/500) (37/80) lowTIParameters4 where
  full := (98543610989/1000000000000)
  energy := (707291847877/1000000000000)
  cov := (285208116041/1000000000000)
  schur := (1044824926371/1000000000000)
  cap := (159335079/200000000000)
  W2 := (1823476462177/500000000000)
  V := (29964847/125000000000)
  mass := (11963791/1000000000000)
  rootN := (255541695029/250000000000)
  rootB := (3528179849/125000000000)
  rootU := (11989727441/20000000000)
  rootV := (15482854259/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_4.scalar_checked
  centre := fun n hn => lowFull4_4 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy4 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_4.bound (by norm_num) hn lowTIParameters4_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_5 : FrameRectangleCertificate 10000 11000 (37/80) (463/1000) lowTIParameters5 where
  full := (49309235753/500000000000)
  energy := (176761340913/250000000000)
  cov := (285515731031/1000000000000)
  schur := (209003127627/200000000000)
  cap := (797398809/1000000000000)
  W2 := (3643656857197/1000000000000)
  V := (239977327/1000000000000)
  mass := (545371/50000000000)
  rootN := (1022260063847/1000000000000)
  rootB := (14119125407/500000000000)
  rootU := (299721483193/500000000000)
  rootV := (9682001/625000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_5.scalar_checked
  centre := fun n hn => lowFull4_5 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy5 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_5.bound (by norm_num) hn lowTIParameters5_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_6 : FrameRectangleCertificate 10000 11000 (463/1000) (927/2000) lowTIParameters6 where
  full := (98693333267/1000000000000)
  energy := (44174937243/62500000000)
  cov := (142785497079/500000000000)
  schur := (522142147059/500000000000)
  cap := (49852807/62500000000)
  W2 := (91009207217/25000000000)
  V := (7500743/31250000000)
  mass := (9950479/1000000000000)
  rootN := (204380458373/200000000000)
  rootB := (5648521619/200000000000)
  rootU := (299699883521/500000000000)
  rootV := (15492700733/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_6.scalar_checked
  centre := fun n hn => lowFull4_6 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy6 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_6.bound (by norm_num) hn lowTIParameters6_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_7 : FrameRectangleCertificate 10000 11000 (927/2000) (58/125) lowTIParameters7 where
  full := (98768196419/1000000000000)
  energy := (141310548901/200000000000)
  cov := (57175667453/200000000000)
  schur := (261118766269/250000000000)
  cap := (79836773/100000000000)
  W2 := (1818543596627/500000000000)
  V := (2402821/10000000000)
  mass := (567703/62500000000)
  rootN := (510997814349/500000000000)
  rootB := (5651080357/200000000000)
  rootU := (599356773797/1000000000000)
  rootV := (310020709/20000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_7.scalar_checked
  centre := fun n hn => lowFull4_7 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy7 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_7.bound (by norm_num) hn lowTIParameters7_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_8 : FrameRectangleCertificate 10000 11000 (58/125) (929/2000) lowTIParameters8 where
  full := (12355382639/125000000000)
  energy := (35315330471/50000000000)
  cov := (142966561519/500000000000)
  schur := (1043744678267/1000000000000)
  cap := (798612909/1000000000000)
  W2 := (363381354553/100000000000)
  V := (240328147/1000000000000)
  mass := (259281/31250000000)
  rootN := (1021638232579/1000000000000)
  rootB := (14129870037/500000000000)
  rootU := (599313986447/1000000000000)
  rootV := (15502520667/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_8.scalar_checked
  centre := fun n hn => lowFull4_8 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy8 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_8.bound (by norm_num) hn lowTIParameters8_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_9 : FrameRectangleCertificate 10000 11000 (929/2000) (93/200) lowTIParameters9 where
  full := (19783585499/200000000000)
  energy := (353030295273/500000000000)
  cov := (286240194621/1000000000000)
  schur := (521967753343/500000000000)
  cap := (399667567/500000000000)
  W2 := (1815273660039/500000000000)
  V := (240586243/1000000000000)
  mass := (7583859/1000000000000)
  rootN := (510865810827/500000000000)
  rootB := (7068128881/250000000000)
  rootU := (59927140477/100000000000)
  rootV := (3877710689/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_9.scalar_checked
  centre := fun n hn => lowFull4_9 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy9 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_9.bound (by norm_num) hn lowTIParameters9_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_10 : FrameRectangleCertificate 10000 11000 (93/200) (931/2000) lowTIParameters10 where
  full := (2474819893/25000000000)
  energy := (705814687803/1000000000000)
  cov := (57258900693/200000000000)
  schur := (1043206070741/1000000000000)
  cap := (799579387/1000000000000)
  W2 := (725457698343/200000000000)
  V := (240631889/1000000000000)
  mass := (1387357/200000000000)
  rootN := (510687299319/500000000000)
  rootB := (28276834813/1000000000000)
  rootU := (74903628571/125000000000)
  rootV := (15512314109/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_10.scalar_checked
  centre := fun n hn => lowFull4_10 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy10 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_10.bound (by norm_num) hn lowTIParameters10_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_11 : FrameRectangleCertificate 10000 11000 (931/2000) (233/500) lowTIParameters11 where
  full := (12383458243/125000000000)
  energy := (705568901107/1000000000000)
  cov := (286601303887/1000000000000)
  schur := (1043396954911/1000000000000)
  cap := (800301023/1000000000000)
  W2 := (3624037035373/1000000000000)
  V := (240889757/1000000000000)
  mass := (3174707/500000000000)
  rootN := (204293607821/200000000000)
  rootB := (28289592133/1000000000000)
  rootU := (299593428829/500000000000)
  rootV := (15520623603/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_11.scalar_checked
  centre := fun n hn => lowFull4_11 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy11 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_11.bound (by norm_num) hn lowTIParameters11_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_12 : FrameRectangleCertificate 10000 11000 (233/500) (933/2000) lowTIParameters12 where
  full := (49571269161/500000000000)
  energy := (88165403797/125000000000)
  cov := (57331027339/200000000000)
  schur := (1042668465311/1000000000000)
  cap := (200136089/250000000000)
  W2 := (452599115751/125000000000)
  V := (240935003/1000000000000)
  mass := (232641/40000000000)
  rootN := (1021111387319/1000000000000)
  rootB := (28293892557/1000000000000)
  rootU := (119828978369/200000000000)
  rootV := (15522081143/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_12.scalar_checked
  centre := fun n hn => lowFull4_12 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy12 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_12.bound (by norm_num) hn lowTIParameters12_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_13 : FrameRectangleCertificate 10000 11000 (933/2000) (467/1000) lowTIParameters13 where
  full := (19843482603/200000000000)
  energy := (352538837763/500000000000)
  cov := (57392333263/200000000000)
  schur := (1042859403523/1000000000000)
  cap := (801265403/1000000000000)
  W2 := (452194517347/125000000000)
  V := (241192643/1000000000000)
  mass := (666433/125000000000)
  rootN := (102120487833/100000000000)
  rootB := (5661326357/200000000000)
  rootU := (7488789137/12500000000)
  rootV := (15530378071/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_13.scalar_checked
  centre := fun n hn => lowFull4_13 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy13 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_13.bound (by norm_num) hn lowTIParameters13_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_14 : FrameRectangleCertificate 10000 11000 (467/1000) (187/400) lowTIParameters14 where
  full := (99292290183/1000000000000)
  energy := (704832236477/1000000000000)
  cov := (17938438997/62500000000)
  schur := (1042131855661/1000000000000)
  cap := (100188477/125000000000)
  W2 := (225895415559/62500000000)
  V := (24123749/100000000000)
  mass := (305693/62500000000)
  rootN := (63803037241/62500000000)
  rootB := (28310913373/1000000000000)
  rootU := (119812314967/200000000000)
  rootV := (15531821851/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_14.scalar_checked
  centre := fun n hn => lowFull4_14 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy14 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_14.bound (by norm_num) hn lowTIParameters14_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_15 : FrameRectangleCertificate 10000 11000 (187/400) (117/250) lowTIParameters15 where
  full := (99367169991/1000000000000)
  energy := (88073364143/125000000000)
  cov := (71830320783/250000000000)
  schur := (208464569251/200000000000)
  cap := (401114139/500000000000)
  W2 := (902776107951/250000000000)
  V := (241494903/1000000000000)
  mass := (561339/125000000000)
  rootN := (510471068293/500000000000)
  rootB := (28323634619/1000000000000)
  rootU := (599020223307/1000000000000)
  rootV := (7770053137/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_15.scalar_checked
  centre := fun n hn => lowFull4_15 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy15 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_15.bound (by norm_num) hn lowTIParameters15_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_16 : FrameRectangleCertificate 10000 11000 (117/250) (937/2000) lowTIParameters16 where
  full := (99442052603/1000000000000)
  energy := (140868341089/200000000000)
  cov := (287374166013/1000000000000)
  schur := (1041596233923/1000000000000)
  cap := (401234889/500000000000)
  W2 := (1803944731411/500000000000)
  V := (241539351/1000000000000)
  mass := (2063281/500000000000)
  rootN := (12757327759/12500000000)
  rootB := (14163948761/500000000000)
  rootU := (598979076219/1000000000000)
  rootV := (3108307263/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_16.scalar_checked
  centre := fun n hn => lowFull4_16 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy16 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_16.bound (by norm_num) hn lowTIParameters16_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_17 : FrameRectangleCertificate 10000 11000 (937/2000) (469/1000) lowTIParameters17 where
  full := (24879234547/250000000000)
  energy := (704096613301/1000000000000)
  cov := (287680155109/1000000000000)
  schur := (260446818811/250000000000)
  cap := (803189653/1000000000000)
  W2 := (180234085881/50000000000)
  V := (30224567/125000000000)
  mass := (118601/31250000000)
  rootN := (204135962069/200000000000)
  rootB := (7085150197/250000000000)
  rootU := (598938133433/1000000000000)
  rootV := (15549808231/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_17.scalar_checked
  centre := fun n hn => lowFull4_17 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy17 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_17.bound (by norm_num) hn lowTIParameters17_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_18 : FrameRectangleCertificate 10000 11000 (469/1000) (939/2000) lowTIParameters18 where
  full := (99591826917/1000000000000)
  energy := (703851636627/1000000000000)
  cov := (287732564087/1000000000000)
  schur := (104106159389/100000000000)
  cap := (803430241/1000000000000)
  W2 := (3601481171819/1000000000000)
  V := (120920293/500000000000)
  mass := (3493649/1000000000000)
  rootN := (102032425919/100000000000)
  rootB := (7086211263/250000000000)
  rootU := (598897394809/1000000000000)
  rootV := (15551224583/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_18.scalar_checked
  centre := fun n hn => lowFull4_18 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy18 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_18.bound (by norm_num) hn lowTIParameters18_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_19 : FrameRectangleCertificate 10000 11000 (939/2000) (47/100) lowTIParameters19 where
  full := (99666718963/1000000000000)
  energy := (351803387671/500000000000)
  cov := (57607656691/200000000000)
  schur := (520626342149/500000000000)
  cap := (25129673/31250000000)
  W2 := (3598287801279/1000000000000)
  V := (48419509/200000000000)
  mass := (20119/6250000000)
  rootN := (1020417896893/1000000000000)
  rootB := (28357530499/1000000000000)
  rootU := (23954274409/40000000000)
  rootV := (7779742043/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_19.scalar_checked
  centre := fun n hn => lowFull4_19 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy19 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_19.bound (by norm_num) hn lowTIParameters19_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_20 : FrameRectangleCertificate 10000 11000 (47/100) (941/2000) lowTIParameters20 where
  full := (99741614501/1000000000000)
  energy := (703362029363/1000000000000)
  cov := (144045109461/500000000000)
  schur := (1040527927761/1000000000000)
  cap := (402194607/500000000000)
  W2 := (3595101581813/1000000000000)
  V := (242141197/1000000000000)
  mass := (1484449/500000000000)
  rootN := (12750783847/12500000000)
  rootB := (28361756187/1000000000000)
  rootU := (598816529553/1000000000000)
  rootV := (972555423/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_20.scalar_checked
  centre := fun n hn => lowFull4_20 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy20 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_20.bound (by norm_num) hn lowTIParameters20_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_21 : FrameRectangleCertificate 10000 11000 (941/2000) (471/1000) lowTIParameters21 where
  full := (99816513707/1000000000000)
  energy := (175779349653/250000000000)
  cov := (288395668921/1000000000000)
  schur := (1040719065641/1000000000000)
  cap := (80510793/100000000000)
  W2 := (3591922489543/1000000000000)
  V := (242397929/1000000000000)
  mass := (2740957/1000000000000)
  rootN := (1020156392737/1000000000000)
  rootB := (28374423871/1000000000000)
  rootU := (119755280537/200000000000)
  rootV := (486535433/31250000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_21.scalar_checked
  centre := fun n hn => lowFull4_21 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy21 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_21.bound (by norm_num) hn lowTIParameters21_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_22 : FrameRectangleCertificate 10000 11000 (471/1000) (943/2000) lowTIParameters22 where
  full := (49945708381/500000000000)
  energy := (702872883003/1000000000000)
  cov := (288701119161/1000000000000)
  schur := (260227577803/250000000000)
  cap := (25182081/31250000000)
  W2 := (897187625119/250000000000)
  V := (242654661/1000000000000)
  mass := (2533171/1000000000000)
  rootN := (31882816309/31250000000)
  rootB := (28387084951/1000000000000)
  rootU := (74842059939/125000000000)
  rootV := (15577376577/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_22.scalar_checked
  centre := fun n hn => lowFull4_22 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy22 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_22.bound (by norm_num) hn lowTIParameters22_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_23 : FrameRectangleCertificate 10000 11000 (943/2000) (59/125) lowTIParameters23 where
  full := (99966323851/1000000000000)
  energy := (702628482457/1000000000000)
  cov := (289006569641/1000000000000)
  schur := (260275416027/250000000000)
  cap := (403272599/500000000000)
  W2 := (1792792795439/500000000000)
  V := (121455697/500000000000)
  mass := (292961/125000000000)
  rootN := (510171947511/500000000000)
  rootB := (28399739401/1000000000000)
  rootU := (598696759949/1000000000000)
  rootV := (15585614971/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_23.scalar_checked
  centre := fun n hn => lowFull4_23 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy23 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_23.bound (by norm_num) hn lowTIParameters23_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_24 : FrameRectangleCertificate 10000 11000 (59/125) (189/400) lowTIParameters24 where
  full := (25010308789/250000000000)
  energy := (140476839379/200000000000)
  cov := (7232800509/25000000000)
  schur := (1041293123999/1000000000000)
  cap := (100907969/125000000000)
  W2 := (1791213868571/500000000000)
  V := (243168127/1000000000000)
  mass := (135677/62500000000)
  rootN := (204087542393/200000000000)
  rootB := (28412387299/1000000000000)
  rootU := (299328621953/500000000000)
  rootV := (3898462253/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_24.scalar_checked
  centre := fun n hn => lowFull4_24 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy24 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_24.bound (by norm_num) hn lowTIParameters24_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_25 : FrameRectangleCertificate 10000 11000 (189/400) (473/1000) lowTIParameters25 where
  full := (20023230173/200000000000)
  energy := (351070013117/500000000000)
  cov := (289617471319/1000000000000)
  schur := (65092793157/62500000000)
  cap := (201995563/250000000000)
  W2 := (715855383127/200000000000)
  V := (12171243/50000000000)
  mass := (2013089/1000000000000)
  rootN := (1020531572521/1000000000000)
  rootB := (1421251431/50000000000)
  rootU := (5986179313/10000000000)
  rootV := (3900519677/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_25.scalar_checked
  centre := fun n hn => lowFull4_25 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy25 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_25.bound (by norm_num) hn lowTIParameters25_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_26 : FrameRectangleCertificate 10000 11000 (473/1000) (947/2000) lowTIParameters26 where
  full := (100191071169/1000000000000)
  energy := (350947985197/500000000000)
  cov := (72480730629/250000000000)
  schur := (520838181649/500000000000)
  cap := (404350349/500000000000)
  W2 := (3576133102939/1000000000000)
  V := (243681593/1000000000000)
  mass := (373817/200000000000)
  rootN := (1020625476509/1000000000000)
  rootB := (28437663371/1000000000000)
  rootU := (598578822067/1000000000000)
  rootV := (3122060813/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_26.scalar_checked
  centre := fun n hn => lowFull4_26 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy26 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_26.bound (by norm_num) hn lowTIParameters26_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_27 : FrameRectangleCertificate 10000 11000 (947/2000) (237/500) lowTIParameters27 where
  full := (100265996259/1000000000000)
  energy := (701652029291/1000000000000)
  cov := (145114186977/500000000000)
  schur := (1041868142011/1000000000000)
  cap := (202354773/250000000000)
  W2 := (1786498137827/500000000000)
  V := (121969163/500000000000)
  mass := (217197/125000000000)
  rootN := (510359711873/500000000000)
  rootB := (14225145799/500000000000)
  rootU := (598539916137/1000000000000)
  rootV := (15618525091/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_27.scalar_checked
  centre := fun n hn => lowFull4_27 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy27 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_27.bound (by norm_num) hn lowTIParameters27_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_28 : FrameRectangleCertificate 10000 11000 (237/500) (949/2000) lowTIParameters28 where
  full := (100340926333/1000000000000)
  energy := (701408202847/1000000000000)
  cov := (72633456407/250000000000)
  schur := (1042060026271/1000000000000)
  cap := (810137433/1000000000000)
  W2 := (1784933205271/500000000000)
  V := (12209753/50000000000)
  mass := (404359/250000000000)
  rootN := (510406707017/500000000000)
  rootB := (28462913291/1000000000000)
  rootU := (119700242693/200000000000)
  rootV := (15626741823/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_28.scalar_checked
  centre := fun n hn => lowFull4_28 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy28 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_28.bound (by norm_num) hn lowTIParameters28_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_29 : FrameRectangleCertificate 10000 11000 (949/2000) (19/40) lowTIParameters29 where
  full := (100415861587/1000000000000)
  energy := (87645561373/125000000000)
  cov := (14541963877/50000000000)
  schur := (41690080631/40000000000)
  cap := (810855723/1000000000000)
  W2 := (1783371742269/500000000000)
  V := (122225897/500000000000)
  mass := (376911/250000000000)
  rootN := (510453723607/500000000000)
  rootB := (14237764247/500000000000)
  rootU := (59846271401/100000000000)
  rootV := (7817477119/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_29.scalar_checked
  centre := fun n hn => lowFull4_29 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy29 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_29.bound (by norm_num) hn lowTIParameters29_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_30 : FrameRectangleCertificate 10000 11000 (19/40) (951/2000) lowTIParameters30 where
  full := (100490802221/1000000000000)
  energy := (350460446809/500000000000)
  cov := (291144729691/1000000000000)
  schur := (1042444110159/1000000000000)
  cap := (20289349/25000000000)
  W2 := (1781813737263/500000000000)
  V := (15294283/62500000000)
  mass := (1407273/1000000000000)
  rootN := (510500761547/500000000000)
  rootB := (28488137181/1000000000000)
  rootU := (9350381527/15625000000)
  rootV := (15643162341/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_30.scalar_checked
  centre := fun n hn => lowFull4_30 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy30 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_30.bound (by norm_num) hn lowTIParameters30_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_31 : FrameRectangleCertificate 10000 11000 (951/2000) (119/250) lowTIParameters31 where
  full := (100565748441/1000000000000)
  energy := (700677410671/1000000000000)
  cov := (145725091039/500000000000)
  schur := (41705452363/40000000000)
  cap := (203073037/250000000000)
  W2 := (3560518357621/1000000000000)
  V := (122482631/500000000000)
  mass := (328871/250000000000)
  rootN := (1021095641493/1000000000000)
  rootB := (2850073943/100000000000)
  rootU := (149596581151/250000000000)
  rootV := (15651366139/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_31.scalar_checked
  centre := fun n hn => lowFull4_31 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy31 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_31.bound (by norm_num) hn lowTIParameters31_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_32 : FrameRectangleCertificate 10000 11000 (119/250) (953/2000) lowTIParameters32 where
  full := (2012814009/20000000000)
  energy := (350217021031/500000000000)
  cov := (2917556347/10000000000)
  schur := (104282861217/100000000000)
  cap := (203252571/250000000000)
  W2 := (3557416110931/1000000000000)
  V := (61305499/250000000000)
  mass := (615757/500000000000)
  rootN := (510594901113/500000000000)
  rootB := (28513335197/1000000000000)
  rootU := (598348434607/1000000000000)
  rootV := (15659565639/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_32.scalar_checked
  centre := fun n hn => lowFull4_32 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy32 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_32.bound (by norm_num) hn lowTIParameters32_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_33 : FrameRectangleCertificate 10000 11000 (953/2000) (477/1000) lowTIParameters33 where
  full := (50357829229/500000000000)
  energy := (700190787709/1000000000000)
  cov := (7301527189/25000000000)
  schur := (1043021019113/1000000000000)
  cap := (813728371/1000000000000)
  W2 := (355432071173/100000000000)
  V := (245478731/1000000000000)
  mass := (115467/100000000000)
  rootN := (797878129/781250000)
  rootB := (28525924543/1000000000000)
  rootU := (598310747733/1000000000000)
  rootV := (15667760881/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_33.scalar_checked
  centre := fun n hn => lowFull4_33 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy33 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_33.bound (by norm_num) hn lowTIParameters33_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_34 : FrameRectangleCertificate 10000 11000 (477/1000) (191/400) lowTIParameters34 where
  full := (100790622677/1000000000000)
  energy := (349973823769/500000000000)
  cov := (292366540653/1000000000000)
  schur := (1043213529561/1000000000000)
  cap := (814446407/1000000000000)
  W2 := (3551232137431/1000000000000)
  V := (49147093/200000000000)
  mass := (271081/250000000000)
  rootN := (204275649999/200000000000)
  rootB := (14269253721/500000000000)
  rootU := (149568315997/250000000000)
  rootV := (7837975903/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_34.scalar_checked
  centre := fun n hn => lowFull4_34 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy34 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_34.bound (by norm_num) hn lowTIParameters34_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_35 : FrameRectangleCertificate 10000 11000 (191/400) (239/500) lowTIParameters35 where
  full := (100865593321/1000000000000)
  energy := (349852310731/500000000000)
  cov := (2286499953/7812500000)
  schur := (1043406143181/1000000000000)
  cap := (163032879/200000000000)
  W2 := (3548150365443/1000000000000)
  V := (1229961/5000000000)
  mass := (509953/500000000000)
  rootN := (40858901467/40000000000)
  rootB := (5710216791/200000000000)
  rootU := (299117991687/500000000000)
  rootV := (3136827697/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_35.scalar_checked
  centre := fun n hn => lowFull4_35 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy35 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_35.bound (by norm_num) hn lowTIParameters35_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_36 : FrameRectangleCertificate 10000 11000 (239/500) (957/2000) lowTIParameters36 where
  full := (100940570609/1000000000000)
  energy := (699461709407/1000000000000)
  cov := (292977447549/1000000000000)
  schur := (1043598859639/1000000000000)
  cap := (815882333/1000000000000)
  W2 := (3545075373381/1000000000000)
  V := (30781117/125000000000)
  mass := (7507/7812500000)
  rootN := (1021566864987/1000000000000)
  rootB := (3570456757/125000000000)
  rootU := (299099452959/500000000000)
  rootV := (627692837/40000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_36.scalar_checked
  centre := fun n hn => lowFull4_36 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy36 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_36.bound (by norm_num) hn lowTIParameters36_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_37 : FrameRectangleCertificate 10000 11000 (957/2000) (479/1000) lowTIParameters37 where
  full := (101015554759/1000000000000)
  energy := (699218911291/1000000000000)
  cov := (58656580269/200000000000)
  schur := (521895839289/500000000000)
  cap := (32664009/40000000000)
  W2 := (3542007138889/1000000000000)
  V := (246505671/1000000000000)
  mass := (906821/1000000000000)
  rootN := (127707654343/125000000000)
  rootB := (14288108911/500000000000)
  rootU := (14954050791/25000000000)
  rootV := (15700499069/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_37.scalar_checked
  centre := fun n hn => lowFull4_37 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy37 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_37.bound (by norm_num) hn lowTIParameters37_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_38 : FrameRectangleCertificate 10000 11000 (479/1000) (959/2000) lowTIParameters38 where
  full := (20218109199/200000000000)
  energy := (349488113519/500000000000)
  cov := (146794177689/500000000000)
  schur := (260996149927/250000000000)
  cap := (817318067/1000000000000)
  W2 := (110592051243/31250000000)
  V := (246762407/1000000000000)
  mass := (428627/500000000000)
  rootN := (1021755645793/1000000000000)
  rootB := (28588775193/1000000000000)
  rootU := (598125360583/1000000000000)
  rootV := (15708672987/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_38.scalar_checked
  centre := fun n hn => lowFull4_38 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy38 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_38.bound (by norm_num) hn lowTIParameters38_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_39 : FrameRectangleCertificate 10000 11000 (959/2000) (12/25) lowTIParameters39 where
  full := (101165544543/1000000000000)
  energy := (139746731313/200000000000)
  cov := (73473452411/250000000000)
  schur := (1044177622663/1000000000000)
  cap := (102254483/125000000000)
  W2 := (1767945426921/500000000000)
  V := (123509571/500000000000)
  mass := (811803/1000000000000)
  rootN := (510925048971/500000000000)
  rootB := (28601326263/1000000000000)
  rootU := (299044446393/500000000000)
  rootV := (7858421311/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_39.scalar_checked
  centre := fun n hn => lowFull4_39 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy39 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_39.bound (by norm_num) hn lowTIParameters39_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_40 : FrameRectangleCertificate 10000 11000 (12/25) (961/2000) lowTIParameters40 where
  full := (101240550633/1000000000000)
  energy := (698491199793/1000000000000)
  cov := (291626119991/1000000000000)
  schur := (1035243402601/1000000000000)
  cap := (813898109/1000000000000)
  W2 := (3532842759047/1000000000000)
  V := (122556569/500000000000)
  mass := (385057/500000000000)
  rootN := (1017469116289/1000000000000)
  rootB := (28528899541/1000000000000)
  rootU := (149513157077/250000000000)
  rootV := (15656089487/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_40.scalar_checked
  centre := fun n hn => lowFull4_40 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy40 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_40.bound (by norm_num) hn lowTIParameters40_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_41 : FrameRectangleCertificate 10000 11000 (961/2000) (481/1000) lowTIParameters41 where
  full := (6332222781/62500000000)
  energy := (698248856647/1000000000000)
  cov := (72982223893/250000000000)
  schur := (517717465057/500000000000)
  cap := (81461117/100000000000)
  W2 := (3529801333489/1000000000000)
  V := (245367623/1000000000000)
  mass := (365931/500000000000)
  rootN := (1017563231507/1000000000000)
  rootB := (1141655759/40000000000)
  rootU := (598016567213/1000000000000)
  rootV := (15664214727/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_41.scalar_checked
  centre := fun n hn => lowFull4_41 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy41 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_41.bound (by norm_num) hn lowTIParameters41_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_42 : FrameRectangleCertificate 10000 11000 (481/1000) (963/2000) lowTIParameters42 where
  full := (198028489/1953125000)
  energy := (349003313523/500000000000)
  cov := (36528958923/125000000000)
  schur := (517813278803/500000000000)
  cap := (203831047/250000000000)
  W2 := (3526766555337/1000000000000)
  V := (245622107/1000000000000)
  mass := (348377/500000000000)
  rootN := (1017657387143/1000000000000)
  rootB := (7138470547/250000000000)
  rootU := (29899035479/50000000000)
  rootV := (15672335723/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_42.scalar_checked
  centre := fun n hn => lowFull4_42 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy42 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_42.bound (by norm_num) hn lowTIParameters42_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_43 : FrameRectangleCertificate 10000 11000 (963/2000) (241/500) lowTIParameters43 where
  full := (12683202061/125000000000)
  energy := (697764510909/1000000000000)
  cov := (292534447423/1000000000000)
  schur := (103581828471/100000000000)
  cap := (20400929/25000000000)
  W2 := (704747680551/200000000000)
  V := (15367287/62500000000)
  mass := (664519/1000000000000)
  rootN := (508875791503/500000000000)
  rootB := (28566364137/1000000000000)
  rootU := (119589011097/200000000000)
  rootV := (3136090509/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_43.scalar_checked
  centre := fun n hn => lowFull4_43 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy43 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_43.bound (by norm_num) hn lowTIParameters43_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_44 : FrameRectangleCertificate 10000 11000 (241/500) (193/400) lowTIParameters44 where
  full := (12692581887/125000000000)
  energy := (348761254081/500000000000)
  cov := (58567444739/200000000000)
  schur := (16187657987/15625000000)
  cap := (816750089/1000000000000)
  W2 := (3520716854187/1000000000000)
  V := (246131077/1000000000000)
  mass := (126983/200000000000)
  rootN := (1017845818957/1000000000000)
  rootB := (14289419941/500000000000)
  rootU := (298954802513/500000000000)
  rootV := (980535323/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_44.scalar_checked
  centre := fun n hn => lowFull4_44 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy44 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_44.bound (by norm_num) hn lowTIParameters44_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_45 : FrameRectangleCertificate 10000 11000 (193/400) (483/1000) lowTIParameters45 where
  full := (50807851219/500000000000)
  energy := (174320154681/250000000000)
  cov := (293140000193/1000000000000)
  schur := (518101018309/500000000000)
  cap := (817462971/1000000000000)
  W2 := (439712736003/125000000000)
  V := (123192781/500000000000)
  mass := (303859/500000000000)
  rootN := (1017940094809/1000000000000)
  rootB := (14295654681/500000000000)
  rootU := (298937179153/500000000000)
  rootV := (15696673597/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_45.scalar_checked
  centre := fun n hn => lowFull4_45 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy45 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_45.bound (by norm_num) hn lowTIParameters45_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_46 : FrameRectangleCertificate 10000 11000 (483/1000) (967/2000) lowTIParameters46 where
  full := (101690758763/1000000000000)
  energy := (348519421259/500000000000)
  cov := (293442776919/1000000000000)
  schur := (518197030383/500000000000)
  cap := (204543953/250000000000)
  W2 := (3514693482837/1000000000000)
  V := (246640047/1000000000000)
  mass := (145681/250000000000)
  rootN := (254508602601/250000000000)
  rootB := (28603772689/1000000000000)
  rootU := (597839315443/1000000000000)
  rootV := (196309723/12500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_46.scalar_checked
  centre := fun n hn => lowFull4_46 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy46 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_46.bound (by norm_num) hn lowTIParameters46_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_47 : FrameRectangleCertificate 10000 11000 (967/2000) (121/250) lowTIParameters47 where
  full := (101765824319/1000000000000)
  energy := (87099647433/125000000000)
  cov := (293745553873/1000000000000)
  schur := (207317236653/200000000000)
  cap := (81888861/100000000000)
  W2 := (3511691617181/1000000000000)
  V := (246894533/1000000000000)
  mass := (139937/250000000000)
  rootN := (1018128765563/1000000000000)
  rootB := (7154057459/250000000000)
  rootU := (119560895309/200000000000)
  rootV := (3142575587/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_47.scalar_checked
  centre := fun n hn => lowFull4_47 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy47 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_47.bound (by norm_num) hn lowTIParameters47_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_48 : FrameRectangleCertificate 10000 11000 (121/250) (969/2000) lowTIParameters48 where
  full := (101840899363/1000000000000)
  energy := (348277814743/500000000000)
  cov := (294048331053/1000000000000)
  schur := (103677840383/100000000000)
  cap := (819601367/1000000000000)
  W2 := (877174067463/250000000000)
  V := (123574509/500000000000)
  mass := (538621/1000000000000)
  rootN := (1018223160133/1000000000000)
  rootB := (28628680847/1000000000000)
  rootU := (597769841757/1000000000000)
  rootV := (628838953/40000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_48.scalar_checked
  centre := fun n hn => lowFull4_48 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy48 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_48.bound (by norm_num) hn lowTIParameters48_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_49 : FrameRectangleCertificate 10000 11000 (969/2000) (97/200) lowTIParameters49 where
  full := (12739498019/125000000000)
  energy := (348157096253/500000000000)
  cov := (147175554231/500000000000)
  schur := (518485361077/500000000000)
  cap := (820314081/1000000000000)
  W2 := (701141483931/200000000000)
  V := (15462719/62500000000)
  mass := (129797/250000000000)
  rootN := (1018317593953/1000000000000)
  rootB := (14320562847/500000000000)
  rootU := (298867705609/500000000000)
  rootV := (786453279/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_49.scalar_checked
  centre := fun n hn => lowFull4_49 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy49 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_49.bound (by norm_num) hn lowTIParameters49_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_50 : FrameRectangleCertificate 10000 11000 (97/200) (971/2000) lowTIParameters50 where
  full := (101991078947/1000000000000)
  energy := (139214573689/200000000000)
  cov := (58930777219/200000000000)
  schur := (207432627579/200000000000)
  cap := (410513377/500000000000)
  W2 := (3502725045463/1000000000000)
  V := (24765799/100000000000)
  mass := (501307/1000000000000)
  rootN := (203682413369/200000000000)
  rootB := (28653564421/1000000000000)
  rootU := (597701185077/1000000000000)
  rootV := (7868576587/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_50.scalar_checked
  centre := fun n hn => lowFull4_50 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy50 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_50.bound (by norm_num) hn lowTIParameters50_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_51 : FrameRectangleCertificate 10000 11000 (971/2000) (243/500) lowTIParameters51 where
  full := (51033092007/500000000000)
  energy := (695831657229/1000000000000)
  cov := (58991332791/200000000000)
  schur := (1037355650777/1000000000000)
  cap := (821739387/1000000000000)
  W2 := (139989965053/40000000000)
  V := (61978119/250000000000)
  mass := (9697/20000000000)
  rootN := (509253289331/500000000000)
  rootB := (28665997053/1000000000000)
  rootU := (37354197719/62500000000)
  rootV := (7872618307/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_51.scalar_checked
  centre := fun n hn => lowFull4_51 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy51 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_51.bound (by norm_num) hn lowTIParameters51_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_52 : FrameRectangleCertificate 10000 11000 (243/500) (973/2000) lowTIParameters52 where
  full := (102141299619/1000000000000)
  energy := (86948819847/125000000000)
  cov := (7381486051/25000000000)
  schur := (1037548260463/1000000000000)
  cap := (411225989/500000000000)
  W2 := (874194910319/250000000000)
  V := (248166963/1000000000000)
  mass := (469699/1000000000000)
  rootN := (254650282307/250000000000)
  rootB := (14339211781/500000000000)
  rootU := (597633346661/1000000000000)
  rootV := (15753315937/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_52.scalar_checked
  centre := fun n hn => lowFull4_52 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy52 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_52.bound (by norm_num) hn lowTIParameters52_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_53 : FrameRectangleCertificate 10000 11000 (973/2000) (487/1000) lowTIParameters53 where
  full := (20443285207/200000000000)
  energy := (69534957301/100000000000)
  cov := (295562220351/1000000000000)
  schur := (207548193333/200000000000)
  cap := (205791133/250000000000)
  W2 := (873454142381/250000000000)
  V := (248421449/1000000000000)
  mass := (227873/500000000000)
  rootN := (101869571839/100000000000)
  rootB := (5738168809/200000000000)
  rootU := (298799867369/500000000000)
  rootV := (985086943/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_53.scalar_checked
  centre := fun n hn => lowFull4_53 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy53 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_53.bound (by norm_num) hn lowTIParameters53_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_54 : FrameRectangleCertificate 10000 11000 (487/1000) (39/80) lowTIParameters54 where
  full := (6393222721/62500000000)
  energy := (43444293741/62500000000)
  cov := (295864998887/1000000000000)
  schur := (1037933769079/1000000000000)
  cap := (411938523/500000000000)
  W2 := (3490859890363/1000000000000)
  V := (7771123/31250000000)
  mass := (110723/250000000000)
  rootN := (1018790345989/1000000000000)
  rootB := (28703258457/1000000000000)
  rootU := (298783163963/500000000000)
  rootV := (3153892427/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_54.scalar_checked
  centre := fun n hn => lowFull4_54 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy54 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_54.bound (by norm_num) hn lowTIParameters54_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_55 : FrameRectangleCertificate 10000 11000 (39/80) (61/125) lowTIParameters55 where
  full := (102366712403/1000000000000)
  energy := (694867939233/1000000000000)
  cov := (296167777647/1000000000000)
  schur := (1038126667389/1000000000000)
  cap := (824589521/1000000000000)
  W2 := (34879095831/10000000000)
  V := (248930423/1000000000000)
  mass := (431049/1000000000000)
  rootN := (1018885011859/1000000000000)
  rootB := (14357833411/500000000000)
  rootU := (59753312643/100000000000)
  rootV := (15777529053/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_55.scalar_checked
  centre := fun n hn => lowFull4_55 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy55 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_55.bound (by norm_num) hn lowTIParameters55_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_56 : FrameRectangleCertificate 10000 11000 (61/125) (977/2000) lowTIParameters56 where
  full := (25610468229/250000000000)
  energy := (173656822767/250000000000)
  cov := (296470556631/1000000000000)
  schur := (1038319661299/1000000000000)
  cap := (20632549/25000000000)
  W2 := (1742482813613/500000000000)
  V := (24918491/100000000000)
  mass := (105033/250000000000)
  rootN := (1018979715843/1000000000000)
  rootB := (28728069201/1000000000000)
  rootU := (298750065231/500000000000)
  rootV := (15785591849/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_56.scalar_checked
  centre := fun n hn => lowFull4_56 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy56 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_56.bound (by norm_num) hn lowTIParameters56_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_57 : FrameRectangleCertificate 10000 11000 (977/2000) (489/1000) lowTIParameters57 where
  full := (102517045361/1000000000000)
  energy := (8679834441/12500000000)
  cov := (74193333959/250000000000)
  schur := (32453523453/31250000000)
  cap := (20650359/25000000000)
  W2 := (435253500283/125000000000)
  V := (124719699/500000000000)
  mass := (410067/1000000000000)
  rootN := (1019074457779/1000000000000)
  rootB := (574809311/20000000000)
  rootU := (597467340243/1000000000000)
  rootV := (24677579/1562500000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_57.scalar_checked
  centre := fun n hn => lowFull4_57 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy57 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_57.bound (by norm_num) hn lowTIParameters57_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_58 : FrameRectangleCertificate 10000 11000 (489/1000) (979/2000) lowTIParameters58 where
  full := (102592230027/1000000000000)
  energy := (694146331799/1000000000000)
  cov := (4641814301/15625000000)
  schur := (1038705934707/1000000000000)
  cap := (413363363/500000000000)
  W2 := (3479096687901/1000000000000)
  V := (49938777/200000000000)
  mass := (25049/62500000000)
  rootN := (12739615469/12500000000)
  rootB := (28752855963/1000000000000)
  rootU := (597434756013/1000000000000)
  rootV := (1580170513/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_58.scalar_checked
  centre := fun n hn => lowFull4_58 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy58 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_58.bound (by norm_num) hn lowTIParameters58_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_59 : FrameRectangleCertificate 10000 11000 (979/2000) (49/100) lowTIParameters59 where
  full := (102667427209/1000000000000)
  energy := (346953010271/500000000000)
  cov := (297378894917/1000000000000)
  schur := (1038899213633/1000000000000)
  cap := (827439053/1000000000000)
  W2 := (3476171663793/1000000000000)
  V := (249948373/1000000000000)
  mass := (392221/1000000000000)
  rootN := (1019264054911/1000000000000)
  rootB := (28765240361/1000000000000)
  rootU := (18668824313/31250000000)
  rootV := (3952438907/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_59.scalar_checked
  centre := fun n hn => lowFull4_59 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy59 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_59.bound (by norm_num) hn lowTIParameters59_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_60 : FrameRectangleCertificate 10000 11000 (49/100) (981/2000) lowTIParameters60 where
  full := (102742637203/1000000000000)
  energy := (173416455359/250000000000)
  cov := (295088806567/1000000000000)
  schur := (1030049222707/1000000000000)
  cap := (411632039/500000000000)
  W2 := (1736626454871/500000000000)
  V := (248023543/1000000000000)
  mass := (384319/1000000000000)
  rootN := (1014913406507/1000000000000)
  rootB := (28692578797/1000000000000)
  rootU := (298685103253/500000000000)
  rootV := (7874381611/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_60.scalar_checked
  centre := fun n hn => lowFull4_60 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy60 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_60.bound (by norm_num) hn lowTIParameters60_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_61 : FrameRectangleCertificate 10000 11000 (981/2000) (491/1000) lowTIParameters61 where
  full := (102817860309/1000000000000)
  energy := (346712867201/500000000000)
  cov := (295388942007/1000000000000)
  schur := (1030240997013/1000000000000)
  cap := (411985881/500000000000)
  W2 := (1735170202827/500000000000)
  V := (7758619/31250000000)
  mass := (15081/40000000000)
  rootN := (63437992517/62500000000)
  rootB := (14352454163/500000000000)
  rootU := (597338241747/1000000000000)
  rootV := (3939192557/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_61.scalar_checked
  centre := fun n hn => lowFull4_61 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy61 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_61.bound (by norm_num) hn lowTIParameters61_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_62 : FrameRectangleCertificate 10000 11000 (491/1000) (983/2000) lowTIParameters62 where
  full := (102893096833/1000000000000)
  energy := (693185759367/1000000000000)
  cov := (147844538833/500000000000)
  schur := (515216432163/500000000000)
  cap := (206169853/250000000000)
  W2 := (433429266443/125000000000)
  V := (124264037/500000000000)
  mass := (370291/1000000000000)
  rootN := (63443899441/62500000000)
  rootB := (2871723197/100000000000)
  rootU := (298653242013/500000000000)
  rootV := (15764773199/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_62.scalar_checked
  centre := fun n hn => lowFull4_62 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy62 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_62.bound (by norm_num) hn lowTIParameters62_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_63 : FrameRectangleCertificate 10000 11000 (983/2000) (123/250) lowTIParameters63 where
  full := (102968347083/1000000000000)
  energy := (346472948127/500000000000)
  cov := (59197842709/200000000000)
  schur := (515312412177/500000000000)
  cap := (82538703/100000000000)
  W2 := (3464534067429/1000000000000)
  V := (248780339/1000000000000)
  mass := (45509/125000000000)
  rootN := (203039387741/200000000000)
  rootB := (28729549771/1000000000000)
  rootU := (4778199469/8000000000)
  rootV := (7886386039/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_63.scalar_checked
  centre := fun n hn => lowFull4_63 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy63 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_63.bound (by norm_num) hn lowTIParameters63_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_64 : FrameRectangleCertificate 10000 11000 (123/250) (197/400) lowTIParameters64 where
  full := (103043611371/1000000000000)
  energy := (346353072493/500000000000)
  cov := (296289349641/1000000000000)
  schur := (515408438403/500000000000)
  cap := (103261827/125000000000)
  W2 := (1730820096737/500000000000)
  V := (49806521/200000000000)
  mass := (358327/1000000000000)
  rootN := (203058304613/200000000000)
  rootB := (3592732717/125000000000)
  rootU := (597243590843/1000000000000)
  rootV := (7890383467/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_64.scalar_checked
  centre := fun n hn => lowFull4_64 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy64 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_64.bound (by norm_num) hn lowTIParameters64_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_65 : FrameRectangleCertificate 10000 11000 (197/400) (493/1000) lowTIParameters65 where
  full := (3222465313/31250000000)
  energy := (346233252743/500000000000)
  cov := (74147371489/250000000000)
  schur := (257752255347/250000000000)
  cap := (82680217/100000000000)
  W2 := (3458752489883/1000000000000)
  V := (249284871/1000000000000)
  mass := (176509/500000000000)
  rootN := (1015386143981/1000000000000)
  rootB := (449283873/15625000000)
  rootU := (597212455997/1000000000000)
  rootV := (15788757741/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_65.scalar_checked
  centre := fun n hn => lowFull4_65 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy65 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_65.bound (by norm_num) hn lowTIParameters65_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_66 : FrameRectangleCertificate 10000 11000 (493/1000) (987/2000) lowTIParameters66 where
  full := (51597091667/500000000000)
  energy := (8652837221/12500000000)
  cov := (37111202811/125000000000)
  schur := (51560062891/50000000000)
  cap := (206877423/250000000000)
  W2 := (215991933563/62500000000)
  V := (249537137/1000000000000)
  mass := (348111/1000000000000)
  rootN := (507740400653/500000000000)
  rootB := (7191617047/250000000000)
  rootU := (597181529397/1000000000000)
  rootV := (15796744507/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_66.scalar_checked
  centre := fun n hn => lowFull4_66 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy66 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_66.bound (by norm_num) hn lowTIParameters66_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_67 : FrameRectangleCertificate 10000 11000 (987/2000) (247/500) lowTIParameters67 where
  full := (103269491651/1000000000000)
  energy := (691987561493/1000000000000)
  cov := (148594879617/500000000000)
  schur := (1031393585811/1000000000000)
  cap := (25881787/31250000000)
  W2 := (3452995515243/1000000000000)
  V := (62447351/250000000000)
  mass := (171787/500000000000)
  rootN := (507787747443/500000000000)
  rootB := (14389381363/500000000000)
  rootU := (597150811381/1000000000000)
  rootV := (3951181817/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_67.scalar_checked
  centre := fun n hn => lowFull4_67 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy67 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_67.bound (by norm_num) hn lowTIParameters67_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_68 : FrameRectangleCertificate 10000 11000 (247/500) (989/2000) lowTIParameters68 where
  full := (103344815297/1000000000000)
  energy := (691748256849/1000000000000)
  cov := (1487449481/5000000000)
  schur := (1031586005109/1000000000000)
  cap := (828924647/1000000000000)
  W2 := (690025241021/200000000000)
  V := (25004167/100000000000)
  mass := (169689/500000000000)
  rootN := (507835112293/500000000000)
  rootB := (2879105151/100000000000)
  rootU := (5971203023/10000000000)
  rootV := (988294123/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_68.scalar_checked
  centre := fun n hn => lowFull4_68 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy68 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_68.bound (by norm_num) hn lowTIParameters68_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_69 : FrameRectangleCertificate 10000 11000 (989/2000) (99/200) lowTIParameters69 where
  full := (103420154603/1000000000000)
  energy := (691509063673/1000000000000)
  cov := (297790033381/1000000000000)
  schur := (1031778515407/1000000000000)
  cap := (829632081/1000000000000)
  W2 := (861815746783/250000000000)
  V := (250293937/1000000000000)
  mass := (335497/1000000000000)
  rootN := (203152998049/200000000000)
  rootB := (28803334547/1000000000000)
  rootU := (597090002501/1000000000000)
  rootV := (632827227/40000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_69.scalar_checked
  centre := fun n hn => lowFull4_69 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy69 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_69.bound (by norm_num) hn lowTIParameters69_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_70 : FrameRectangleCertificate 10000 11000 (99/200) (991/2000) lowTIParameters70 where
  full := (25873877477/250000000000)
  energy := (691269981889/1000000000000)
  cov := (11923606831/40000000000)
  schur := (206394223283/200000000000)
  cap := (415169743/500000000000)
  W2 := (861101460491/250000000000)
  V := (62636551/250000000000)
  mass := (165953/500000000000)
  rootN := (1015859791711/1000000000000)
  rootB := (5763122369/200000000000)
  rootU := (298529956179/500000000000)
  rootV := (3957162841/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_70.scalar_checked
  centre := fun n hn => lowFull4_70 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy70 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_70.bound (by norm_num) hn lowTIParameters70_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_71 : FrameRectangleCertificate 10000 11000 (991/2000) (62/125) lowTIParameters71 where
  full := (103570881551/1000000000000)
  energy := (345515505711/500000000000)
  cov := (298390308387/1000000000000)
  schur := (1032163807889/1000000000000)
  cap := (51940429/62500000000)
  W2 := (1720777375193/500000000000)
  V := (250798471/1000000000000)
  mass := (328583/1000000000000)
  rootN := (507977314427/500000000000)
  rootB := (28827883447/1000000000000)
  rootU := (298515016123/500000000000)
  rootV := (7918309021/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_71.scalar_checked
  centre := fun n hn => lowFull4_71 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy71 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_71.bound (by norm_num) hn lowTIParameters71_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_72 : FrameRectangleCertificate 10000 11000 (62/125) (993/2000) lowTIParameters72 where
  full := (103646269877/1000000000000)
  energy := (345396076099/500000000000)
  cov := (74672611553/250000000000)
  schur := (41294263581/40000000000)
  cap := (166350843/200000000000)
  W2 := (3438709693179/1000000000000)
  V := (125525369/500000000000)
  mass := (162753/500000000000)
  rootN := (508024750757/500000000000)
  rootB := (28840149359/1000000000000)
  rootU := (597000362553/1000000000000)
  rootV := (7922290357/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_72.scalar_checked
  centre := fun n hn => lowFull4_72 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy72 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_72.bound (by norm_num) hn lowTIParameters72_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_73 : FrameRectangleCertificate 10000 11000 (993/2000) (497/1000) lowTIParameters73 where
  full := (103721675237/1000000000000)
  energy := (690553404141/1000000000000)
  cov := (74747646063/250000000000)
  schur := (16133585329/15625000000)
  cap := (832461541/1000000000000)
  W2 := (3435870651247/1000000000000)
  V := (125651503/500000000000)
  mass := (322657/1000000000000)
  rootN := (1016144409549/1000000000000)
  rootB := (28852409623/1000000000000)
  rootU := (149242725921/250000000000)
  rootV := (15852539419/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_73.scalar_checked
  centre := fun n hn => lowFull4_73 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy73 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_73.bound (by norm_num) hn lowTIParameters73_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_74 : FrameRectangleCertificate 10000 11000 (497/1000) (199/400) lowTIParameters74 where
  full := (20759419597/200000000000)
  energy := (690314767177/1000000000000)
  cov := (149645361253/500000000000)
  schur := (516371211107/500000000000)
  cap := (833168839/1000000000000)
  W2 := (137321504223/40000000000)
  V := (251555273/1000000000000)
  mass := (160009/500000000000)
  rootN := (508119676409/500000000000)
  rootB := (14432332097/500000000000)
  rootU := (298470828027/500000000000)
  rootV := (15860494097/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_74.scalar_checked
  centre := fun n hn => lowFull4_74 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy74 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_74.bound (by norm_num) hn lowTIParameters74_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_75 : FrameRectangleCertificate 10000 11000 (199/400) (249/500) lowTIParameters75 where
  full := (103872538477/1000000000000)
  energy := (690076241231/1000000000000)
  cov := (299590860971/1000000000000)
  schur := (1032935472711/1000000000000)
  cap := (833876113/1000000000000)
  W2 := (3430210537227/1000000000000)
  V := (251807541/1000000000000)
  mass := (317573/1000000000000)
  rootN := (1016334331169/1000000000000)
  rootB := (28876913149/1000000000000)
  rootU := (298456310041/500000000000)
  rootV := (793422241/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_75.scalar_checked
  centre := fun n hn => lowFull4_75 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy75 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_75.bound (by norm_num) hn lowTIParameters75_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_76 : FrameRectangleCertificate 10000 11000 (249/500) (997/2000) lowTIParameters76 where
  full := (103947997079/1000000000000)
  energy := (172459456557/250000000000)
  cov := (5997819993/20000000000)
  schur := (516564306141/500000000000)
  cap := (208645841/250000000000)
  W2 := (856847356831/250000000000)
  V := (252059809/1000000000000)
  mass := (78827/250000000000)
  rootN := (508214672231/500000000000)
  rootB := (28889156513/1000000000000)
  rootU := (149220949053/250000000000)
  rootV := (7938195781/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_76.scalar_checked
  centre := fun n hn => lowFull4_76 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy76 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_76.bound (by norm_num) hn lowTIParameters76_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_77 : FrameRectangleCertificate 10000 11000 (997/2000) (499/1000) lowTIParameters77 where
  full := (104023474157/1000000000000)
  energy := (344799761047/500000000000)
  cov := (300191138541/1000000000000)
  schur := (516660920329/500000000000)
  cap := (83529059/100000000000)
  W2 := (3424574257109/1000000000000)
  V := (252312077/1000000000000)
  mass := (313207/1000000000000)
  rootN := (203304878511/200000000000)
  rootB := (14450697129/500000000000)
  rootU := (596855184893/1000000000000)
  rootV := (15884334327/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_77.scalar_checked
  centre := fun n hn => lowFull4_77 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy77 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_77.bound (by norm_num) hn lowTIParameters77_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_78 : FrameRectangleCertificate 10000 11000 (499/1000) (999/2000) lowTIParameters78 where
  full := (52049485041/500000000000)
  energy := (344680664379/500000000000)
  cov := (300491277643/1000000000000)
  schur := (1033515157583/1000000000000)
  cap := (167199559/200000000000)
  W2 := (3421765007921/1000000000000)
  V := (50512869/200000000000)
  mass := (15563/50000000000)
  rootN := (63538717207/62500000000)
  rootB := (28913626459/1000000000000)
  rootU := (596826786587/1000000000000)
  rootV := (15892273123/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_78.scalar_checked
  centre := fun n hn => lowFull4_78 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy78 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_78.bound (by norm_num) hn lowTIParameters78_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_79 : FrameRectangleCertificate 10000 11000 (999/2000) (1/2) lowTIParameters79 where
  full := (104174485231/1000000000000)
  energy := (689123246139/1000000000000)
  cov := (150395708479/500000000000)
  schur := (516854281387/500000000000)
  cap := (836704979/1000000000000)
  W2 := (3418961661061/1000000000000)
  V := (126408307/500000000000)
  mass := (154727/500000000000)
  rootN := (203342918517/200000000000)
  rootB := (9256273/320000000)
  rootU := (596798601763/1000000000000)
  rootV := (15900207987/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_79.scalar_checked
  centre := fun n hn => lowFull4_79 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy79 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_79.bound (by norm_num) hn lowTIParameters79_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_80 : FrameRectangleCertificate 10000 11000 (1/2) (1001/2000) lowTIParameters80 where
  full := (6515626249/62500000000)
  energy := (688885274171/1000000000000)
  cov := (18654952539/62500000000)
  schur := (1024939439591/1000000000000)
  cap := (20812339/25000000000)
  W2 := (3416164198061/1000000000000)
  V := (250873219/1000000000000)
  mass := (307779/1000000000000)
  rootN := (101239292747/100000000000)
  rootB := (28852964493/1000000000000)
  rootU := (59677063091/100000000000)
  rootV := (197987223/12500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_80.scalar_checked
  centre := fun n hn => lowFull4_80 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy80 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_80.bound (by norm_num) hn lowTIParameters80_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_81 : FrameRectangleCertificate 10000 11000 (1001/2000) (501/1000) lowTIParameters81 where
  full := (104325574729/1000000000000)
  energy := (68864741277/100000000000)
  cov := (2987767691/10000000000)
  schur := (1025131333119/1000000000000)
  cap := (833196191/1000000000000)
  W2 := (3413372600339/1000000000000)
  V := (251123293/1000000000000)
  mass := (12249/40000000000)
  rootN := (1012487695293/1000000000000)
  rootB := (28865137987/1000000000000)
  rootU := (149185718631/250000000000)
  rootV := (15846870133/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_81.scalar_checked
  centre := fun n hn => lowFull4_81 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy81 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_81.bound (by norm_num) hn lowTIParameters81_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_82 : FrameRectangleCertificate 10000 11000 (501/1000) (1003/2000) lowTIParameters82 where
  full := (104401149853/1000000000000)
  energy := (688409661873/1000000000000)
  cov := (37384287223/125000000000)
  schur := (205064662677/200000000000)
  cap := (2084747/2500000000)
  W2 := (3410586849679/1000000000000)
  V := (251373367/1000000000000)
  mass := (152391/500000000000)
  rootN := (1012582497077/1000000000000)
  rootB := (28877305969/1000000000000)
  rootU := (233091927/390625000)
  rootV := (7927379249/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_82.scalar_checked
  centre := fun n hn => lowFull4_82 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy82 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_82.bound (by norm_num) hn lowTIParameters82_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_83 : FrameRectangleCertificate 10000 11000 (1003/2000) (251/500) lowTIParameters83 where
  full := (20895349151/200000000000)
  energy := (3440860107/5000000000)
  cov := (74842956669/250000000000)
  schur := (128189422511/125000000000)
  cap := (417300697/500000000000)
  W2 := (3407806927633/1000000000000)
  V := (125811721/500000000000)
  mass := (303443/1000000000000)
  rootN := (1012677332663/1000000000000)
  rootB := (14444734283/500000000000)
  rootU := (596688007221/1000000000000)
  rootV := (15862642971/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_83.scalar_checked
  centre := fun n hn => lowFull4_83 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy83 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_83.bound (by norm_num) hn lowTIParameters83_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_84 : FrameRectangleCertificate 10000 11000 (251/500) (201/400) lowTIParameters84 where
  full := (6534522677/62500000000)
  energy := (687934491279/1000000000000)
  cov := (1170583421/3906250000)
  schur := (16026680203/15625000000)
  cap := (83530397/100000000000)
  W2 := (3405032816039/1000000000000)
  V := (62968379/250000000000)
  mass := (1511/5000000000)
  rootN := (40510888077/40000000000)
  rootB := (28901625733/1000000000000)
  rootU := (7458261217/12500000000)
  rootV := (3174104699/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_84.scalar_checked
  centre := fun n hn => lowFull4_84 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy84 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_84.bound (by norm_num) hn lowTIParameters84_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_85 : FrameRectangleCertificate 10000 11000 (201/400) (503/1000) lowTIParameters85 where
  full := (10462800149/100000000000)
  energy := (171924267859/250000000000)
  cov := (299966885081/1000000000000)
  schur := (512949885917/500000000000)
  cap := (6531301/7812500000)
  W2 := (106320765523/31250000000)
  V := (252123591/1000000000000)
  mass := (60209/200000000000)
  rootN := (40514684189/40000000000)
  rootB := (14456888739/500000000000)
  rootU := (74579250511/125000000000)
  rootV := (793920007/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_85.scalar_checked
  centre := fun n hn => lowFull4_85 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy85 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_85.bound (by norm_num) hn lowTIParameters85_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_86 : FrameRectangleCertificate 10000 11000 (503/1000) (1007/2000) lowTIParameters86 where
  full := (104703662139/1000000000000)
  energy := (3437298809/5000000000)
  cov := (2345815739/7812500000)
  schur := (20521841927/20000000000)
  cap := (836709071/1000000000000)
  W2 := (3399501951637/1000000000000)
  V := (126186833/500000000000)
  mass := (74993/250000000000)
  rootN := (1012962040923/1000000000000)
  rootB := (14462961929/500000000000)
  rootU := (18643978999/31250000000)
  rootV := (198578411/12500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_86.scalar_checked
  centre := fun n hn => lowFull4_86 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy86 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_86.bound (by norm_num) hn lowTIParameters86_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_87 : FrameRectangleCertificate 10000 11000 (1007/2000) (63/125) lowTIParameters87 where
  full := (13097418149/125000000000)
  energy := (137444512459/200000000000)
  cov := (30056194431/100000000000)
  schur := (513142253147/500000000000)
  cap := (2093529/2500000000)
  W2 := (339674516273/100000000000)
  V := (252623741/1000000000000)
  mass := (9343/31250000000)
  rootN := (1013057010387/1000000000000)
  rootB := (14469032449/500000000000)
  rootU := (596580869569/1000000000000)
  rootV := (397353543/25000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_87.scalar_checked
  centre := fun n hn => lowFull4_87 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy87 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_87.bound (by norm_num) hn lowTIParameters87_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_88 : FrameRectangleCertificate 10000 11000 (63/125) (1009/2000) lowTIParameters88 where
  full := (1638360173/15625000000)
  energy := (686985472849/1000000000000)
  cov := (150429737117/500000000000)
  schur := (1026477001411/1000000000000)
  cap := (419057057/500000000000)
  W2 := (1696997056039/500000000000)
  V := (31609227/125000000000)
  mass := (298049/1000000000000)
  rootN := (1013152012983/1000000000000)
  rootB := (28950200587/1000000000000)
  rootU := (298277314743/500000000000)
  rootV := (7951003333/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_88.scalar_checked
  centre := fun n hn => lowFull4_88 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy88 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_88.bound (by norm_num) hn lowTIParameters88_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_89 : FrameRectangleCertificate 10000 11000 (1009/2000) (101/200) lowTIParameters89 where
  full := (524653901/5000000000)
  energy := (686748493389/1000000000000)
  cov := (301157004361/1000000000000)
  schur := (1026669581437/1000000000000)
  cap := (167763323/200000000000)
  W2 := (1695624390937/500000000000)
  V := (63280973/250000000000)
  mass := (74297/250000000000)
  rootN := (1013247048571/1000000000000)
  rootB := (28962330967/1000000000000)
  rootU := (74566076039/125000000000)
  rootV := (3977466939/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_89.scalar_checked
  centre := fun n hn => lowFull4_89 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy89 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_89.bound (by norm_num) hn lowTIParameters89_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_90 : FrameRectangleCertificate 10000 11000 (101/200) (1011/2000) lowTIParameters90 where
  full := (105006533007/1000000000000)
  energy := (343255811921/500000000000)
  cov := (60290906939/200000000000)
  schur := (1026862246141/1000000000000)
  cap := (419759551/500000000000)
  W2 := (3388509154291/1000000000000)
  V := (15835873/62500000000)
  mass := (296387/1000000000000)
  rootN := (253335529257/250000000000)
  rootB := (14487228013/500000000000)
  rootU := (298251403331/500000000000)
  rootV := (3979431241/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_90.scalar_checked
  centre := fun n hn => lowFull4_90 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy90 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_90.bound (by norm_num) hn lowTIParameters90_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_91 : FrameRectangleCertificate 10000 11000 (1011/2000) (253/500) lowTIParameters91 where
  full := (10508230993/100000000000)
  energy := (137254972827/200000000000)
  cov := (30175206523/100000000000)
  schur := (1027054995243/1000000000000)
  cap := (840221579/1000000000000)
  W2 := (338577521163/100000000000)
  V := (253624043/1000000000000)
  mass := (147821/500000000000)
  rootN := (202687443641/200000000000)
  rootB := (14493287921/500000000000)
  rootU := (596477225167/1000000000000)
  rootV := (15925578263/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_91.scalar_checked
  centre := fun n hn => lowFull4_91 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy91 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_91.bound (by norm_num) hn lowTIParameters91_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_92 : FrameRectangleCertificate 10000 11000 (253/500) (1013/2000) lowTIParameters92 where
  full := (105158111407/1000000000000)
  energy := (343019107099/500000000000)
  cov := (302049595969/1000000000000)
  schur := (41089913141/40000000000)
  cap := (168184809/200000000000)
  W2 := (135321877453/40000000000)
  V := (253874119/1000000000000)
  mass := (294949/1000000000000)
  rootN := (253383087997/250000000000)
  rootB := (14499345201/500000000000)
  rootU := (596451864467/1000000000000)
  rootV := (15933427723/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_92.scalar_checked
  centre := fun n hn => lowFull4_92 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy92 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_92.bound (by norm_num) hn lowTIParameters92_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_93 : FrameRectangleCertificate 10000 11000 (1013/2000) (507/1000) lowTIParameters93 where
  full := (26308484471/250000000000)
  energy := (685801673953/1000000000000)
  cov := (151173563457/500000000000)
  schur := (1027440745721/1000000000000)
  cap := (841626501/1000000000000)
  W2 := (3380324310709/1000000000000)
  V := (63531049/250000000000)
  mass := (58861/200000000000)
  rootN := (506813759117/500000000000)
  rootB := (29010799731/1000000000000)
  rootU := (596426725207/1000000000000)
  rootV := (318825467/20000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_93.scalar_checked
  centre := fun n hn => lowFull4_93 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy93 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_93.bound (by norm_num) hn lowTIParameters93_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_94 : FrameRectangleCertificate 10000 11000 (507/1000) (203/400) lowTIParameters94 where
  full := (26327447453/250000000000)
  energy := (171391310833/250000000000)
  cov := (151322329029/500000000000)
  schur := (513816873293/500000000000)
  cap := (210582237/250000000000)
  W2 := (3377607317397/1000000000000)
  V := (1987299/7812500000)
  mass := (58741/200000000000)
  rootN := (202744543363/200000000000)
  rootB := (7255725963/250000000000)
  rootU := (119280361613/200000000000)
  rootV := (7974557543/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_94.scalar_checked
  centre := fun n hn => lowFull4_94 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy94 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_94.bound (by norm_num) hn lowTIParameters94_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_95 : FrameRectangleCertificate 10000 11000 (203/400) (127/250) lowTIParameters95 where
  full := (105385667647/1000000000000)
  energy := (685328922263/1000000000000)
  cov := (151471094703/500000000000)
  schur := (205565366177/200000000000)
  cap := (843031387/1000000000000)
  W2 := (3374895938943/1000000000000)
  V := (63656087/250000000000)
  mass := (146573/500000000000)
  rootN := (202763589521/200000000000)
  rootB := (2903500279/100000000000)
  rootU := (596377113717/1000000000000)
  rootV := (1994619121/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_95.scalar_checked
  centre := fun n hn => lowFull4_95 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy95 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_95.bound (by norm_num) hn lowTIParameters95_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_96 : FrameRectangleCertificate 10000 11000 (127/250) (1017/2000) lowTIParameters96 where
  full := (2109231437/20000000000)
  energy := (685092710671/1000000000000)
  cov := (60647944191/200000000000)
  schur := (25700499959/25000000000)
  cap := (42186691/50000000000)
  W2 := (421523769749/125000000000)
  V := (10194977/40000000000)
  mass := (146313/500000000000)
  rootN := (253478302617/250000000000)
  rootB := (5809419317/200000000000)
  rootU := (298176321427/500000000000)
  rootV := (15964787033/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_96.scalar_checked
  centre := fun n hn => lowFull4_96 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy96 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_96.bound (by norm_num) hn lowTIParameters96_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_97 : FrameRectangleCertificate 10000 11000 (1017/2000) (509/1000) lowTIParameters97 where
  full := (105537502889/1000000000000)
  energy := (342428304243/500000000000)
  cov := (303537252707/1000000000000)
  schur := (1028213248767/1000000000000)
  cap := (844436247/1000000000000)
  W2 := (842372489319/250000000000)
  V := (127562251/500000000000)
  mass := (146071/500000000000)
  rootN := (507004252637/500000000000)
  rootB := (7264796311/250000000000)
  rootU := (596328396189/1000000000000)
  rootV := (1996577157/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_97.scalar_checked
  centre := fun n hn => lowFull4_97 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy97 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_97.bound (by norm_num) hn lowTIParameters97_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_98 : FrameRectangleCertificate 10000 11000 (509/1000) (1019/2000) lowTIParameters98 where
  full := (21122692247/200000000000)
  energy := (171155153909/250000000000)
  cov := (151917392329/500000000000)
  schur := (1028406581879/1000000000000)
  cap := (845138667/1000000000000)
  W2 := (1683397659819/500000000000)
  V := (255374579/1000000000000)
  mass := (291691/1000000000000)
  rootN := (1014103831903/1000000000000)
  rootB := (5814253751/200000000000)
  rootU := (596304374441/1000000000000)
  rootV := (15980443643/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_98.scalar_checked
  centre := fun n hn => lowFull4_98 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy98 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_98.bound (by norm_num) hn lowTIParameters98_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_99 : FrameRectangleCertificate 10000 11000 (1019/2000) (51/100) lowTIParameters99 where
  full := (13211180921/125000000000)
  energy := (42774045753/62500000000)
  cov := (304132316811/1000000000000)
  schur := (128574999681/125000000000)
  cap := (211460271/250000000000)
  W2 := (672821245587/200000000000)
  V := (15976541/62500000000)
  mass := (29127/100000000000)
  rootN := (1014199190223/1000000000000)
  rootB := (14541673597/500000000000)
  rootU := (596280578351/1000000000000)
  rootV := (7994133099/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_99.scalar_checked
  centre := fun n hn => lowFull4_99 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy99 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_99.bound (by norm_num) hn lowTIParameters99_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_100 : FrameRectangleCertificate 10000 11000 (51/100) (1021/2000) lowTIParameters100 where
  full := (105765461769/1000000000000)
  energy := (684148957649/1000000000000)
  cov := (75449588763/250000000000)
  schur := (1019908582841/1000000000000)
  cap := (841594053/1000000000000)
  W2 := (672284533011/200000000000)
  V := (5073259/20000000000)
  mass := (145439/500000000000)
  rootN := (201981046917/200000000000)
  rootB := (14505120243/500000000000)
  rootU := (37266063041/62500000000)
  rootV := (7963399871/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_100.scalar_checked
  centre := fun n hn => lowFull4_100 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy100 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_100.bound (by norm_num) hn lowTIParameters100_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_101 : FrameRectangleCertificate 10000 11000 (1021/2000) (511/1000) lowTIParameters101 where
  full := (105841504931/1000000000000)
  energy := (683913292373/1000000000000)
  cov := (302093308693/1000000000000)
  schur := (1020100481557/1000000000000)
  cap := (842292013/1000000000000)
  W2 := (3358744614123/1000000000000)
  V := (12695543/50000000000)
  mass := (290513/1000000000000)
  rootN := (202000047679/200000000000)
  rootB := (14511133769/500000000000)
  rootU := (29811683307/50000000000)
  rootV := (3186916127/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_101.scalar_checked
  centre := fun n hn => lowFull4_101 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy101 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_101.bound (by norm_num) hn lowTIParameters101_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_102 : FrameRectangleCertificate 10000 11000 (511/1000) (1023/2000) lowTIParameters102 where
  full := (52958788673/500000000000)
  energy := (683677736143/1000000000000)
  cov := (151194131267/500000000000)
  schur := (40811698453/40000000000)
  cap := (842989971/1000000000000)
  W2 := (3356072058169/1000000000000)
  V := (25415877/100000000000)
  mass := (290173/1000000000000)
  rootN := (1010095273391/1000000000000)
  rootB := (29034289573/1000000000000)
  rootU := (37263159473/62500000000)
  rootV := (15942357731/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_102.scalar_checked
  centre := fun n hn => lowFull4_102 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy102 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_102.bound (by norm_num) hn lowTIParameters102_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_103 : FrameRectangleCertificate 10000 11000 (1023/2000) (64/125) lowTIParameters103 where
  full := (26498419879/250000000000)
  energy := (683442288889/1000000000000)
  cov := (75670804143/250000000000)
  schur := (255121130469/250000000000)
  cap := (210921983/250000000000)
  W2 := (1676702490163/500000000000)
  V := (254406681/1000000000000)
  mass := (57971/200000000000)
  rootN := (101019033943/100000000000)
  rootB := (5809261337/200000000000)
  rootU := (596187665733/1000000000000)
  rootV := (7975065533/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_103.scalar_checked
  centre := fun n hn => lowFull4_103 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy103 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_103.bound (by norm_num) hn lowTIParameters103_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_104 : FrameRectangleCertificate 10000 11000 (64/125) (41/80) lowTIParameters104 where
  full := (26517452987/250000000000)
  energy := (683206950541/1000000000000)
  cov := (302978170803/1000000000000)
  schur := (510338331491/500000000000)
  cap := (211096473/250000000000)
  W2 := (3350743363851/1000000000000)
  V := (254654591/1000000000000)
  mass := (289559/1000000000000)
  rootN := (1010285436391/1000000000000)
  rootB := (29058318809/1000000000000)
  rootU := (74520626181/125000000000)
  rootV := (15957900583/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_104.scalar_checked
  centre := fun n hn => lowFull4_104 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy104 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_104.bound (by norm_num) hn lowTIParameters104_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_105 : FrameRectangleCertificate 10000 11000 (41/80) (513/1000) lowTIParameters105 where
  full := (53072987577/500000000000)
  energy := (341485860513/500000000000)
  cov := (30327312523/100000000000)
  schur := (127608610551/125000000000)
  cap := (169016771/200000000000)
  W2 := (1674043596007/500000000000)
  V := (127451251/500000000000)
  mass := (289283/1000000000000)
  rootN := (252595141037/250000000000)
  rootB := (14535163011/500000000000)
  rootU := (59614258353/100000000000)
  rootV := (15965666351/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_105.scalar_checked
  centre := fun n hn => lowFull4_105 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy105 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_105.bound (by norm_num) hn lowTIParameters105_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_106 : FrameRectangleCertificate 10000 11000 (513/1000) (1027/2000) lowTIParameters106 where
  full := (106222169653/1000000000000)
  energy := (27309464011/40000000000)
  cov := (151784039927/500000000000)
  schur := (20421223719/20000000000)
  cap := (845781821/1000000000000)
  W2 := (836359112057/250000000000)
  V := (63787603/250000000000)
  mass := (11561/40000000000)
  rootN := (505237861297/500000000000)
  rootB := (29082328329/1000000000000)
  rootU := (596120388821/1000000000000)
  rootV := (15973428311/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_106.scalar_checked
  centre := fun n hn => lowFull4_106 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy106 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_106.bound (by norm_num) hn lowTIParameters106_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_107 : FrameRectangleCertificate 10000 11000 (1027/2000) (257/500) lowTIParameters107 where
  full := (1660912437/15625000000)
  energy := (136500317643/200000000000)
  cov := (18991439667/62500000000)
  schur := (63828347959/62500000000)
  cap := (84647979/100000000000)
  W2 := (3342791115861/1000000000000)
  V := (255398323/1000000000000)
  mass := (18049/62500000000)
  rootN := (1010570911587/1000000000000)
  rootB := (3636790717/125000000000)
  rootU := (298049213081/500000000000)
  rootV := (15981186533/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_107.scalar_checked
  centre := fun n hn => lowFull4_107 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy107 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_107.bound (by norm_num) hn lowTIParameters107_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_108 : FrameRectangleCertificate 10000 11000 (257/500) (1029/2000) lowTIParameters108 where
  full := (106374654631/1000000000000)
  energy := (85283335597/125000000000)
  cov := (152078994843/500000000000)
  schur := (204289205679/200000000000)
  cap := (169435553/200000000000)
  W2 := (3340151178461/1000000000000)
  V := (127823117/500000000000)
  mass := (3607/12500000000)
  rootN := (1010666131023/1000000000000)
  rootB := (29106318301/1000000000000)
  rootU := (149019174107/250000000000)
  rootV := (15988940991/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_108.scalar_checked
  centre := fun n hn => lowFull4_108 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy108 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_108.bound (by norm_num) hn lowTIParameters108_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_109 : FrameRectangleCertificate 10000 11000 (1029/2000) (103/200) lowTIParameters109 where
  full := (106450946179/1000000000000)
  energy := (682031889889/1000000000000)
  cov := (76113236223/250000000000)
  schur := (1021638568851/1000000000000)
  cap := (423937873/500000000000)
  W2 := (52148697181/15625000000)
  V := (127947073/500000000000)
  mass := (5767/20000000000)
  rootN := (31586293149/31250000000)
  rootB := (2911830603/100000000000)
  rootU := (1192110401/2000000000)
  rootV := (15996691721/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_109.scalar_checked
  centre := fun n hn => lowFull4_109 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy109 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_109.bound (by norm_num) hn lowTIParameters109_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_110 : FrameRectangleCertificate 10000 11000 (103/200) (1031/2000) lowTIParameters110 where
  full := (53263635577/500000000000)
  energy := (681797203479/1000000000000)
  cov := (304747900293/1000000000000)
  schur := (49894101/48828125)
  cap := (848573733/1000000000000)
  W2 := (3334887422817/1000000000000)
  V := (256142057/1000000000000)
  mass := (144077/500000000000)
  rootN := (10108566607/10000000000)
  rootB := (910321529/31250000000)
  rootU := (149008484817/250000000000)
  rootV := (8002219333/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_110.scalar_checked
  centre := fun n hn => lowFull4_110 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy110 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_110.bound (by norm_num) hn lowTIParameters110_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_111 : FrameRectangleCertificate 10000 11000 (1031/2000) (129/250) lowTIParameters111 where
  full := (53301815053/500000000000)
  energy := (340781312741/500000000000)
  cov := (152521427943/500000000000)
  schur := (255505971771/250000000000)
  cap := (849271729/1000000000000)
  W2 := (3332263571963/1000000000000)
  V := (256389969/1000000000000)
  mass := (287971/1000000000000)
  rootN := (1010951970711/1000000000000)
  rootB := (14571133527/500000000000)
  rootU := (298006456827/500000000000)
  rootV := (8006090947/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_111.scalar_checked
  centre := fun n hn => lowFull4_111 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy111 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_111.bound (by norm_num) hn lowTIParameters111_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_112 : FrameRectangleCertificate 10000 11000 (129/250) (1033/2000) lowTIParameters112 where
  full := (26670005897/250000000000)
  energy := (340664077911/500000000000)
  cov := (38167226459/125000000000)
  schur := (102221666441/100000000000)
  cap := (169993947/200000000000)
  W2 := (3329645050683/1000000000000)
  V := (6415947/25000000000)
  mass := (1439/5000000000)
  rootN := (1011047310669/1000000000000)
  rootB := (2915424043/100000000000)
  rootU := (74499015571/125000000000)
  rootV := (16019921349/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_112.scalar_checked
  centre := fun n hn => lowFull4_112 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy112 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_112.bound (by norm_num) hn lowTIParameters112_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_113 : FrameRectangleCertificate 10000 11000 (1033/2000) (517/1000) lowTIParameters113 where
  full := (26689113041/250000000000)
  energy := (681093794431/1000000000000)
  cov := (6112655353/20000000000)
  schur := (1022409520251/1000000000000)
  cap := (3402671/4000000000)
  W2 := (1663515921437/500000000000)
  V := (8027681/31250000000)
  mass := (287641/1000000000000)
  rootN := (505571340231/500000000000)
  rootB := (5833241809/200000000000)
  rootU := (119194314593/200000000000)
  rootV := (16027657097/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_113.scalar_checked
  centre := fun n hn => lowFull4_113 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy113 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_113.bound (by norm_num) hn lowTIParameters113_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_114 : FrameRectangleCertificate 10000 11000 (517/1000) (207/400) lowTIParameters114 where
  full := (106832916403/1000000000000)
  energy := (340429770619/500000000000)
  cov := (152963861909/500000000000)
  schur := (1022602454377/1000000000000)
  cap := (851365777/1000000000000)
  W2 := (1662211966211/500000000000)
  V := (32141713/125000000000)
  mass := (287491/1000000000000)
  rootN := (31601189999/31250000000)
  rootB := (7294543239/250000000000)
  rootU := (595951259803/1000000000000)
  rootV := (16035389113/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_114.scalar_checked
  centre := fun n hn => lowFull4_114 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy114 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_114.bound (by norm_num) hn lowTIParameters114_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_115 : FrameRectangleCertificate 10000 11000 (207/400) (259/500) lowTIParameters115 where
  full := (26727354219/250000000000)
  energy := (680625396173/1000000000000)
  cov := (306222680179/1000000000000)
  schur := (255698866641/250000000000)
  cap := (426031909/500000000000)
  W2 := (3321821303257/1000000000000)
  V := (257381617/1000000000000)
  mass := (35919/125000000000)
  rootN := (1011333509069/1000000000000)
  rootB := (29190132203/1000000000000)
  rootU := (595931186043/1000000000000)
  rootV := (8021558717/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_115.scalar_checked
  centre := fun n hn => lowFull4_115 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy115 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_115.bound (by norm_num) hn lowTIParameters115_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_116 : FrameRectangleCertificate 10000 11000 (259/500) (1037/2000) lowTIParameters116 where
  full := (53492977083/500000000000)
  energy := (680391359169/1000000000000)
  cov := (306517636729/1000000000000)
  schur := (511494278303/500000000000)
  cap := (85276187/100000000000)
  W2 := (331922393949/100000000000)
  V := (257629529/1000000000000)
  mass := (287221/1000000000000)
  rootN := (1011428967653/1000000000000)
  rootB := (29202086741/1000000000000)
  rootU := (148977838171/250000000000)
  rootV := (16050842003/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_116.scalar_checked
  centre := fun n hn => lowFull4_116 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy116 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_116.bound (by norm_num) hn lowTIParameters116_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_117 : FrameRectangleCertificate 10000 11000 (1037/2000) (519/1000) lowTIParameters117 where
  full := (5353126443/50000000000)
  energy := (13603148603/20000000000)
  cov := (306812593471/1000000000000)
  schur := (1023181724261/1000000000000)
  cap := (853459939/1000000000000)
  W2 := (663326365021/200000000000)
  V := (257877441/1000000000000)
  mass := (287099/1000000000000)
  rootN := (1011524455593/1000000000000)
  rootB := (14607018339/500000000000)
  rootU := (7448647009/12500000000)
  rootV := (2007320357/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_117.scalar_checked
  centre := fun n hn => lowFull4_117 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy117 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_117.bound (by norm_num) hn lowTIParameters117_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_118 : FrameRectangleCertificate 10000 11000 (519/1000) (1039/2000) lowTIParameters118 where
  full := (53569570777/500000000000)
  energy := (169980902263/250000000000)
  cov := (153553775201/500000000000)
  schur := (1023374969331/1000000000000)
  cap := (106769753/125000000000)
  W2 := (3314044944357/1000000000000)
  V := (129062677/500000000000)
  mass := (57397/200000000000)
  rootN := (505809986391/500000000000)
  rootB := (29225982003/1000000000000)
  rootU := (37242025699/62500000000)
  rootV := (1606628003/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_118.scalar_checked
  centre := fun n hn => lowFull4_118 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy118 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_118.bound (by norm_num) hn lowTIParameters118_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_119 : FrameRectangleCertificate 10000 11000 (1039/2000) (13/25) lowTIParameters119 where
  full := (107215792847/1000000000000)
  energy := (135937979161/200000000000)
  cov := (240158209/781250000)
  schur := (255892072897/250000000000)
  cap := (427428063/500000000000)
  W2 := (827865820363/250000000000)
  V := (258373267/1000000000000)
  mass := (143439/500000000000)
  rootN := (1011715519101/1000000000000)
  rootB := (14618961369/500000000000)
  rootU := (297926652553/500000000000)
  rootV := (16073993499/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_119.scalar_checked
  centre := fun n hn => lowFull4_119 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy119 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_119.bound (by norm_num) hn lowTIParameters119_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_120 : FrameRectangleCertificate 10000 11000 (13/25) (1041/2000) lowTIParameters120 where
  full := (53646241673/500000000000)
  energy := (135891258067/200000000000)
  cov := (76261763033/250000000000)
  schur := (1014951602477/1000000000000)
  cap := (212643593/250000000000)
  W2 := (3308886820641/1000000000000)
  V := (32049187/125000000000)
  mass := (143389/500000000000)
  rootN := (1007448064407/1000000000000)
  rootB := (2916460821/100000000000)
  rootU := (595834443531/1000000000000)
  rootV := (16012292029/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_120.scalar_checked
  centre := fun n hn => lowFull4_120 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy120 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_120.bound (by norm_num) hn lowTIParameters120_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_121 : FrameRectangleCertificate 10000 11000 (1041/2000) (521/1000) lowTIParameters121 where
  full := (107369213667/1000000000000)
  energy := (5306428067/7812500000)
  cov := (954185819/3125000000)
  schur := (1015143404323/1000000000000)
  cap := (425634061/500000000000)
  W2 := (826578886573/250000000000)
  V := (64159817/250000000000)
  mass := (57337/200000000000)
  rootN := (503771625919/500000000000)
  rootB := (14588249741/500000000000)
  rootU := (119163165507/200000000000)
  rootV := (1601996467/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_121.scalar_checked
  centre := fun n hn => lowFull4_121 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy121 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_121.bound (by norm_num) hn lowTIParameters121_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_122 : FrameRectangleCertificate 10000 11000 (521/1000) (1043/2000) lowTIParameters122 where
  full := (6715374027/62500000000)
  energy := (339494701229/500000000000)
  cov := (76407968053/250000000000)
  schur := (1015335282043/1000000000000)
  cap := (851961893/1000000000000)
  W2 := (3303749442819/1000000000000)
  V := (3211063/12500000000)
  mass := (286597/1000000000000)
  rootN := (503819233963/500000000000)
  rootB := (2918838627/100000000000)
  rootU := (595797458203/1000000000000)
  rootV := (16027633637/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_122.scalar_checked
  centre := fun n hn => lowFull4_122 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy122 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_122.bound (by norm_num) hn lowTIParameters122_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_123 : FrameRectangleCertificate 10000 11000 (1043/2000) (261/500) lowTIParameters123 where
  full := (107522796267/1000000000000)
  energy := (84844514989/125000000000)
  cov := (305924282533/1000000000000)
  schur := (253881808861/250000000000)
  cap := (852655687/1000000000000)
  W2 := (3301188494697/1000000000000)
  V := (64282703/250000000000)
  mass := (57303/200000000000)
  rootN := (1007733712567/1000000000000)
  rootB := (7300067153/250000000000)
  rootU := (59577933663/100000000000)
  rootV := (8017649469/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_123.scalar_checked
  centre := fun n hn => lowFull4_123 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy123 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_123.bound (by norm_num) hn lowTIParameters123_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_124 : FrameRectangleCertificate 10000 11000 (261/500) (209/400) lowTIParameters124 where
  full := (10759964981/100000000000)
  energy := (678522944871/1000000000000)
  cov := (306216693037/1000000000000)
  schur := (1015719264313/1000000000000)
  cap := (6666793/7812500000)
  W2 := (824658171629/250000000000)
  V := (32172073/125000000000)
  mass := (143219/500000000000)
  rootN := (1007828985649/1000000000000)
  rootB := (5842429303/200000000000)
  rootU := (119152292789/200000000000)
  rootV := (641718423/40000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_124.scalar_checked
  centre := fun n hn => lowFull4_124 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy124 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_124.bound (by norm_num) hn lowTIParameters124_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_125 : FrameRectangleCertificate 10000 11000 (209/400) (523/1000) lowTIParameters125 where
  full := (1076765457/10000000000)
  energy := (33914493863/50000000000)
  cov := (76627275931/250000000000)
  schur := (1015911368407/1000000000000)
  cap := (170808669/200000000000)
  W2 := (103002562587/31250000000)
  V := (257622357/1000000000000)
  mass := (143183/500000000000)
  rootN := (1007924287041/1000000000000)
  rootB := (29224020001/1000000000000)
  rootU := (37233990079/62500000000)
  rootV := (16050618587/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_125.scalar_checked
  centre := fun n hn => lowFull4_125 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy125 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_125.bound (by norm_num) hn lowTIParameters125_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_126 : FrameRectangleCertificate 10000 11000 (523/1000) (1047/2000) lowTIParameters126 where
  full := (107753484589/1000000000000)
  energy := (84757114627/125000000000)
  cov := (153400757299/500000000000)
  schur := (254025886891/250000000000)
  cap := (213684303/250000000000)
  W2 := (3293536428233/1000000000000)
  V := (25786813/100000000000)
  mass := (286299/1000000000000)
  rootN := (1008019616657/1000000000000)
  rootB := (2923588911/100000000000)
  rootU := (74465808719/125000000000)
  rootV := (8029136473/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_126.scalar_checked
  centre := fun n hn => lowFull4_126 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy126 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_126.bound (by norm_num) hn lowTIParameters126_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_127 : FrameRectangleCertificate 10000 11000 (1047/2000) (131/250) lowTIParameters127 where
  full := (26957616783/250000000000)
  energy := (169456016017/250000000000)
  cov := (153546962827/500000000000)
  schur := (508147900769/500000000000)
  cap := (213857777/250000000000)
  W2 := (658199189513/200000000000)
  V := (129056951/500000000000)
  mass := (71559/250000000000)
  rootN := (201622994873/200000000000)
  rootB := (29247753897/1000000000000)
  rootU := (59570935057/100000000000)
  rootV := (4016480907/250000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_127.scalar_checked
  centre := fun n hn => lowFull4_127 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy127 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_127.bound (by norm_num) hn lowTIParameters127_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_128 : FrameRectangleCertificate 10000 11000 (131/250) (1049/2000) lowTIParameters128 where
  full := (53953746997/500000000000)
  energy := (338795659173/500000000000)
  cov := (153693168447/500000000000)
  schur := (254122032537/250000000000)
  cap := (856125033/1000000000000)
  W2 := (3288460545561/1000000000000)
  V := (64589919/250000000000)
  mass := (286177/1000000000000)
  rootN := (252052590017/250000000000)
  rootB := (29259614369/1000000000000)
  rootU := (595692484903/1000000000000)
  rootV := (1607357073/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_128.scalar_checked
  centre := fun n hn => lowFull4_128 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy128 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_128.bound (by norm_num) hn lowTIParameters128_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_129 : FrameRectangleCertificate 10000 11000 (1049/2000) (21/40) lowTIParameters129 where
  full := (21596913169/200000000000)
  energy := (338679339891/500000000000)
  cov := (153839374159/500000000000)
  schur := (508340266587/500000000000)
  cap := (856818987/1000000000000)
  W2 := (1642965103531/500000000000)
  V := (258605449/1000000000000)
  mass := (286121/1000000000000)
  rootN := (20166115473/20000000000)
  rootB := (29271470531/1000000000000)
  rootU := (595675873951/1000000000000)
  rootV := (3216242833/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_129.scalar_checked
  centre := fun n hn => lowFull4_129 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy129 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_129.bound (by norm_num) hn lowTIParameters129_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_130 : FrameRectangleCertificate 10000 11000 (21/40) (1051/2000) lowTIParameters130 where
  full := (21612336673/200000000000)
  energy := (677126148311/1000000000000)
  cov := (153985579961/500000000000)
  schur := (127109126303/125000000000)
  cap := (214378243/250000000000)
  W2 := (3283404917039/1000000000000)
  V := (129425611/500000000000)
  mass := (286069/1000000000000)
  rootN := (504200607503/500000000000)
  rootB := (29283322421/1000000000000)
  rootU := (595659518941/1000000000000)
  rootV := (1005553373/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_130.scalar_checked
  centre := fun n hn => lowFull4_130 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy130 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_130.bound (by norm_num) hn lowTIParameters130_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_131 : FrameRectangleCertificate 10000 11000 (1051/2000) (263/500) lowTIParameters131 where
  full := (54069423619/500000000000)
  energy := (676893723859/1000000000000)
  cov := (308263571709/1000000000000)
  schur := (127133195209/125000000000)
  cap := (214551747/250000000000)
  W2 := (1640442330183/500000000000)
  V := (64774249/250000000000)
  mass := (14301/50000000000)
  rootN := (1008496684017/1000000000000)
  rootB := (14647585023/500000000000)
  rootU := (119128684219/200000000000)
  rootV := (16096490177/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_131.scalar_checked
  centre := fun n hn => lowFull4_131 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy131 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_131.bound (by norm_num) hn lowTIParameters131_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_132 : FrameRectangleCertificate 10000 11000 (263/500) (1053/2000) lowTIParameters132 where
  full := (54108029079/500000000000)
  energy := (676661406363/1000000000000)
  cov := (154277991839/500000000000)
  schur := (1017258186751/1000000000000)
  cap := (10736263/12500000000)
  W2 := (409796177771/125000000000)
  V := (259342769/1000000000000)
  mass := (11439/40000000000)
  rootN := (63037011287/62500000000)
  rootB := (3663376687/125000000000)
  rootU := (148906895419/250000000000)
  rootV := (8052061367/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_132.scalar_checked
  centre := fun n hn => lowFull4_132 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy132 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_132.bound (by norm_num) hn lowTIParameters132_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_133 : FrameRectangleCertificate 10000 11000 (1053/2000) (527/1000) lowTIParameters133 where
  full := (108293316827/1000000000000)
  energy := (84553649469/125000000000)
  cov := (308848395827/1000000000000)
  schur := (508725442711/500000000000)
  cap := (107449391/125000000000)
  W2 := (3275859187453/1000000000000)
  V := (259588543/1000000000000)
  mass := (71483/250000000000)
  rootN := (504343852303/500000000000)
  rootB := (1172754111/40000000000)
  rootU := (595612001951/1000000000000)
  rootV := (3222350341/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_133.scalar_checked
  centre := fun n hn => lowFull4_133 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy133 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_133.bound (by norm_num) hn lowTIParameters133_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_134 : FrameRectangleCertificate 10000 11000 (527/1000) (211/400) lowTIParameters134 where
  full := (108370623953/1000000000000)
  energy := (16904927299/25000000000)
  cov := (309140808157/1000000000000)
  schur := (508821828757/500000000000)
  cap := (215072313/250000000000)
  W2 := (3273353941447/1000000000000)
  V := (259834317/1000000000000)
  mass := (71473/250000000000)
  rootN := (201756651193/200000000000)
  rootB := (29330687889/1000000000000)
  rootU := (595596683213/1000000000000)
  rootV := (16119377067/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_134.scalar_checked
  centre := fun n hn => lowFull4_134 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy134 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_134.bound (by norm_num) hn lowTIParameters134_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_135 : FrameRectangleCertificate 10000 11000 (211/400) (66/125) lowTIParameters135 where
  full := (108447980251/1000000000000)
  energy := (135193018983/200000000000)
  cov := (309433220667/1000000000000)
  schur := (1017836502803/1000000000000)
  cap := (430491707/500000000000)
  W2 := (3270853669277/1000000000000)
  V := (260080091/1000000000000)
  mass := (142927/500000000000)
  rootN := (1008878834551/1000000000000)
  rootB := (29342518877/1000000000000)
  rootU := (595581626757/1000000000000)
  rootV := (8063499411/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_135.scalar_checked
  centre := fun n hn => lowFull4_135 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy135 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_135.bound (by norm_num) hn lowTIParameters135_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_136 : FrameRectangleCertificate 10000 11000 (66/125) (1057/2000) lowTIParameters136 where
  full := (54262693223/500000000000)
  energy := (84466650569/125000000000)
  cov := (309725633357/1000000000000)
  schur := (509014710553/500000000000)
  cap := (430838807/500000000000)
  W2 := (3268358356249/1000000000000)
  V := (52065173/200000000000)
  mass := (142909/500000000000)
  rootN := (126121805033/125000000000)
  rootB := (1834646609/62500000000)
  rootU := (74445854239/125000000000)
  rootV := (8067308489/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_136.scalar_checked
  centre := fun n hn => lowFull4_136 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy136 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_136.bound (by norm_num) hn lowTIParameters136_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_137 : FrameRectangleCertificate 10000 11000 (1057/2000) (529/1000) lowTIParameters137 where
  full := (108602843269/1000000000000)
  energy := (675501420803/1000000000000)
  cov := (310018046227/1000000000000)
  schur := (254555603053/250000000000)
  cap := (862371857/1000000000000)
  W2 := (130634719507/40000000000)
  V := (6514291/25000000000)
  mass := (57157/200000000000)
  rootN := (504535036497/500000000000)
  rootB := (29366168579/1000000000000)
  rootU := (297776153009/500000000000)
  rootV := (16142231569/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_137.scalar_checked
  centre := fun n hn => lowFull4_137 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy137 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_137.bound (by norm_num) hn lowTIParameters137_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_138 : FrameRectangleCertificate 10000 11000 (529/1000) (1059/2000) lowTIParameters138 where
  full := (108680351461/1000000000000)
  energy := (675269743601/1000000000000)
  cov := (38788807409/125000000000)
  schur := (1018415475927/1000000000000)
  cap := (43153307/50000000000)
  W2 := (3263382548979/1000000000000)
  V := (130408707/500000000000)
  mass := (142877/500000000000)
  rootN := (1009165732637/1000000000000)
  rootB := (14688993669/500000000000)
  rootU := (14888451111/25000000000)
  rootV := (8074921269/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_138.scalar_checked
  centre := fun n hn => lowFull4_138 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy138 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_138.bound (by norm_num) hn lowTIParameters138_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_139 : FrameRectangleCertificate 10000 11000 (1059/2000) (53/100) lowTIParameters139 where
  full := (13594738971/125000000000)
  energy := (168759543219/250000000000)
  cov := (310602872497/1000000000000)
  schur := (127326076507/125000000000)
  cap := (863760469/1000000000000)
  W2 := (652180405107/200000000000)
  V := (261063189/1000000000000)
  mass := (71431/250000000000)
  rootN := (1009261419087/1000000000000)
  rootB := (14694901063/500000000000)
  rootU := (119104810109/200000000000)
  rootV := (8078724977/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_139.scalar_checked
  centre := fun n hn => lowFull4_139 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy139 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_139.bound (by norm_num) hn lowTIParameters139_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_140 : FrameRectangleCertificate 10000 11000 (53/100) (1061/2000) lowTIParameters140 where
  full := (108835524947/1000000000000)
  energy := (134961341713/200000000000)
  cov := (154113104291/500000000000)
  schur := (505031919727/500000000000)
  cap := (429722483/500000000000)
  W2 := (1629213201457/500000000000)
  V := (32383199/125000000000)
  mass := (285697/1000000000000)
  rootN := (502509661463/500000000000)
  rootB := (29316291819/1000000000000)
  rootU := (29775516287/50000000000)
  rootV := (3219102931/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_140.scalar_checked
  centre := fun n hn => lowFull4_140 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy140 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_140.bound (by norm_num) hn lowTIParameters140_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_141 : FrameRectangleCertificate 10000 11000 (1061/2000) (531/1000) lowTIParameters141 where
  full := (108913191761/1000000000000)
  energy := (168643837649/250000000000)
  cov := (30851610503/100000000000)
  schur := (50512772651/50000000000)
  cap := (860135053/1000000000000)
  W2 := (3255955666623/1000000000000)
  V := (259309251/1000000000000)
  mass := (285671/1000000000000)
  rootN := (201022929341/200000000000)
  rootB := (14664029571/500000000000)
  rootU := (74437108929/125000000000)
  rootV := (3220616407/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_141.scalar_checked
  centre := fun n hn => lowFull4_141 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy141 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_141.bound (by norm_num) hn lowTIParameters141_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_142 : FrameRectangleCertificate 10000 11000 (531/1000) (1063/2000) lowTIParameters142 where
  full := (54495456491/500000000000)
  energy := (134868819781/200000000000)
  cov := (77201500413/250000000000)
  schur := (1010447137799/1000000000000)
  cap := (215206297/250000000000)
  W2 := (3253489802311/1000000000000)
  V := (25955291/100000000000)
  mass := (285647/1000000000000)
  rootN := (502604998433/500000000000)
  rootB := (29339822563/1000000000000)
  rootU := (18608865283/31250000000)
  rootV := (805532293/50000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_142.scalar_checked
  centre := fun n hn => lowFull4_142 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy142 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_142.bound (by norm_num) hn lowTIParameters142_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_143 : FrameRectangleCertificate 10000 11000 (1063/2000) (133/250) lowTIParameters143 where
  full := (109068689389/1000000000000)
  energy := (674112953423/1000000000000)
  cov := (19318493653/62500000000)
  schur := (101063889359/100000000000)
  cap := (6892123/8000000000)
  W2 := (1625514397807/500000000000)
  V := (25979657/100000000000)
  mass := (35703/125000000000)
  rootN := (1005305373303/1000000000000)
  rootB := (5870316431/200000000000)
  rootU := (595470780059/1000000000000)
  rootV := (8059103083/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_143.scalar_checked
  centre := fun n hn => lowFull4_143 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy143 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_143.bound (by norm_num) hn lowTIParameters143_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_144 : FrameRectangleCertificate 10000 11000 (133/250) (213/400) lowTIParameters144 where
  full := (27286630443/250000000000)
  energy := (336940957041/500000000000)
  cov := (154692897709/500000000000)
  schur := (1010830720213/1000000000000)
  cap := (862205613/1000000000000)
  W2 := (162428631613/50000000000)
  V := (26004023/100000000000)
  mass := (142801/500000000000)
  rootN := (1005400775917/1000000000000)
  rootB := (29363337907/1000000000000)
  rootU := (297729072957/500000000000)
  rootV := (1007860183/62500000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_144.scalar_checked
  centre := fun n hn => lowFull4_144 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy144 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_144.bound (by norm_num) hn lowTIParameters144_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_145 : FrameRectangleCertificate 10000 11000 (213/400) (533/1000) lowTIParameters145 where
  full := (109224410927/1000000000000)
  energy := (673650980819/1000000000000)
  cov := (154837846281/500000000000)
  schur := (1011022617483/1000000000000)
  cap := (431447951/500000000000)
  W2 := (649224259613/200000000000)
  V := (26028389/100000000000)
  mass := (142791/500000000000)
  rootN := (1005496204609/1000000000000)
  rootB := (14687544911/500000000000)
  rootU := (595445788111/1000000000000)
  rootV := (16133316151/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_145.scalar_checked
  centre := fun n hn => lowFull4_145 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy145 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_145.bound (by norm_num) hn lowTIParameters145_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_146 : FrameRectangleCertificate 10000 11000 (533/1000) (1067/2000) lowTIParameters146 where
  full := (54651178829/500000000000)
  energy := (336710076781/500000000000)
  cov := (309965589879/1000000000000)
  schur := (1011214585199/1000000000000)
  cap := (863586247/1000000000000)
  W2 := (648734955763/200000000000)
  V := (5210551/20000000000)
  mass := (285563/1000000000000)
  rootN := (1005591659273/1000000000000)
  rootB := (2938683799/100000000000)
  rootU := (11908674163/20000000000)
  rootV := (8070432919/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_146.scalar_checked
  centre := fun n hn => lowFull4_146 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy146 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_146.bound (by norm_num) hn lowTIParameters146_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_147 : FrameRectangleCertificate 10000 11000 (1067/2000) (267/500) lowTIParameters147 where
  full := (5469018139/50000000000)
  energy := (2692757729/4000000000)
  cov := (310255487369/1000000000000)
  schur := (505703311597/500000000000)
  cap := (108034581/125000000000)
  W2 := (324123306049/100000000000)
  V := (26077121/100000000000)
  mass := (57109/200000000000)
  rootN := (502843569909/500000000000)
  rootB := (5879716483/200000000000)
  rootU := (37213869223/62500000000)
  rootV := (16148411997/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_147.scalar_checked
  centre := fun n hn => lowFull4_147 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy147 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_147.bound (by norm_num) hn lowTIParameters147_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_148 : FrameRectangleCertificate 10000 11000 (267/500) (1069/2000) lowTIParameters148 where
  full := (54729213557/500000000000)
  energy := (168239704203/250000000000)
  cov := (310545385031/1000000000000)
  schur := (505799365631/500000000000)
  cap := (432483553/500000000000)
  W2 := (404849516121/125000000000)
  V := (26101487/100000000000)
  mass := (285529/1000000000000)
  rootN := (1005782646133/1000000000000)
  rootB := (367629039/12500000000)
  rootU := (595410387901/1000000000000)
  rootV := (1615595463/100000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_148.scalar_checked
  centre := fun n hn => lowFull4_148 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy148 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_148.bound (by norm_num) hn lowTIParameters148_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_149 : FrameRectangleCertificate 10000 11000 (1069/2000) (107/200) lowTIParameters149 where
  full := (27384137873/250000000000)
  energy := (336364153591/500000000000)
  cov := (19427205179/62500000000)
  schur := (202358181843/200000000000)
  cap := (108207203/125000000000)
  W2 := (3236363970269/1000000000000)
  V := (261258531/1000000000000)
  mass := (285513/1000000000000)
  rootN := (1005878178119/1000000000000)
  rootB := (45971969/1562500000)
  rootU := (595399150719/1000000000000)
  rootV := (646539751/40000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_149.scalar_checked
  centre := fun n hn => lowFull4_149 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy149 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_149.bound (by norm_num) hn lowTIParameters149_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_150 : FrameRectangleCertificate 10000 11000 (107/200) (1071/2000) lowTIParameters150 where
  full := (6850921047/62500000000)
  energy := (10507779739/15625000000)
  cov := (31112518087/100000000000)
  schur := (1011983156889/1000000000000)
  cap := (433174101/500000000000)
  W2 := (646787314093/200000000000)
  V := (16343887/62500000000)
  mass := (142749/500000000000)
  rootN := (502986867843/500000000000)
  rootB := (14716896769/500000000000)
  rootU := (595388197603/1000000000000)
  rootV := (3234205881/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_150.scalar_checked
  centre := fun n hn => lowFull4_150 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy150 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_150.bound (by norm_num) hn lowTIParameters150_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_151 : FrameRectangleCertificate 10000 11000 (1071/2000) (67/125) lowTIParameters151 where
  full := (54846491871/500000000000)
  energy := (134453521017/200000000000)
  cov := (62283015809/200000000000)
  schur := (1012175474081/1000000000000)
  cap := (867038843/1000000000000)
  W2 := (1615756957843/500000000000)
  V := (65436463/250000000000)
  mass := (71371/250000000000)
  rootN := (503034659363/500000000000)
  rootB := (29445523311/1000000000000)
  rootU := (595377530157/1000000000000)
  rootV := (8089280747/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_151.scalar_checked
  centre := fun n hn => lowFull4_151 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy151 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_151.bound (by norm_num) hn lowTIParameters151_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_152 : FrameRectangleCertificate 10000 11000 (67/125) (1073/2000) lowTIParameters152 where
  full := (109771293321/1000000000000)
  energy := (336018706243/500000000000)
  cov := (31170497739/100000000000)
  schur := (50618393031/50000000000)
  cap := (216932387/250000000000)
  W2 := (645819198419/200000000000)
  V := (261989513/1000000000000)
  mass := (285471/1000000000000)
  rootN := (1006164927147/1000000000000)
  rootB := (29457249499/1000000000000)
  rootU := (59536715001/100000000000)
  rootV := (16186090109/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_152.scalar_checked
  centre := fun n hn => lowFull4_152 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy152 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_152.bound (by norm_num) hn lowTIParameters152_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_153 : FrameRectangleCertificate 10000 11000 (1073/2000) (537/1000) lowTIParameters153 where
  full := (109849666353/1000000000000)
  energy := (167951831357/250000000000)
  cov := (76170624/244140625)
  schur := (506280158151/500000000000)
  cap := (5427627/6250000000)
  W2 := (1613341392937/500000000000)
  V := (131116587/500000000000)
  mass := (142729/500000000000)
  rootN := (25156514021/25000000000)
  rootB := (14734486079/500000000000)
  rootU := (297678529397/500000000000)
  rootV := (2024201903/125000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_153.scalar_checked
  centre := fun n hn => lowFull4_153 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy153 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_153.bound (by norm_num) hn lowTIParameters153_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_154 : FrameRectangleCertificate 10000 11000 (537/1000) (43/80) lowTIParameters154 where
  full := (109928103713/1000000000000)
  energy := (13431546877/20000000000)
  cov := (31228477459/100000000000)
  schur := (50637642049/50000000000)
  cap := (434555579/500000000000)
  W2 := (806068570841/250000000000)
  V := (65619209/250000000000)
  mass := (285447/1000000000000)
  rootN := (503178109863/500000000000)
  rootB := (1179227651/40000000000)
  rootU := (595347258179/1000000000000)
  rootV := (8100568437/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_154.scalar_checked
  centre := fun n hn => lowFull4_154 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy154 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_154.bound (by norm_num) hn lowTIParameters154_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_155 : FrameRectangleCertificate 10000 11000 (43/80) (269/500) lowTIParameters155 where
  full := (55003303143/500000000000)
  energy := (671347467681/1000000000000)
  cov := (312574673443/1000000000000)
  schur := (1012945434433/1000000000000)
  cap := (434901033/500000000000)
  W2 := (805467617709/250000000000)
  V := (262720497/1000000000000)
  mass := (71359/250000000000)
  rootN := (503225951843/500000000000)
  rootB := (14746203461/500000000000)
  rootU := (119067549969/200000000000)
  rootV := (16208655003/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_155.scalar_checked
  centre := fun n hn => lowFull4_155 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy155 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_155.bound (by norm_num) hn lowTIParameters155_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_156 : FrameRectangleCertificate 10000 11000 (269/500) (1077/2000) lowTIParameters156 where
  full := (22017034993/200000000000)
  energy := (33555884843/50000000000)
  cov := (156432286233/500000000000)
  schur := (1013138096513/1000000000000)
  cap := (870493041/1000000000000)
  W2 := (1609735667359/500000000000)
  V := (131482079/500000000000)
  mass := (11417/40000000000)
  rootN := (1006547612641/1000000000000)
  rootB := (7376029763/250000000000)
  rootU := (297664267749/500000000000)
  rootV := (16216169647/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_156.scalar_checked
  centre := fun n hn => lowFull4_156 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy156 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_156.bound (by norm_num) hn lowTIParameters156_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_157 : FrameRectangleCertificate 10000 11000 (1077/2000) (539/1000) lowTIParameters157 where
  full := (110163810651/1000000000000)
  energy := (670888031319/1000000000000)
  cov := (62630894331/200000000000)
  schur := (506665413517/500000000000)
  cap := (217796023/250000000000)
  W2 := (201067303841/62500000000)
  V := (13160391/50000000000)
  mass := (35677/125000000000)
  rootN := (1006643346491/1000000000000)
  rootB := (14757913911/500000000000)
  rootU := (297659808429/500000000000)
  rootV := (16223680841/1000000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_157.scalar_checked
  centre := fun n hn => lowFull4_157 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy157 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_157.bound (by norm_num) hn lowTIParameters157_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_158 : FrameRectangleCertificate 10000 11000 (539/1000) (1079/2000) lowTIParameters158 where
  full := (6890157141/62500000000)
  energy := (670658470991/1000000000000)
  cov := (78361092753/250000000000)
  schur := (1013523625799/1000000000000)
  cap := (435937609/500000000000)
  W2 := (3214687037497/1000000000000)
  V := (131725741/500000000000)
  mass := (285407/1000000000000)
  rootN := (1006739105131/1000000000000)
  rootB := (1476376661/50000000000)
  rootU := (297655497833/500000000000)
  rootV := (8115594279/500000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_158.scalar_checked
  centre := fun n hn => lowFull4_158 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy158 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_158.bound (by norm_num) hn lowTIParameters158_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangle4_159 : FrameRectangleCertificate 10000 11000 (1079/2000) (27/50) lowTIParameters159 where
  full := (110321286701/1000000000000)
  energy := (670429015813/1000000000000)
  cov := (39216783817/125000000000)
  schur := (20274329853/20000000000)
  cap := (872566419/1000000000000)
  W2 := (50192216397/15625000000)
  V := (32961893/125000000000)
  mass := (142699/500000000000)
  rootN := (40273395539/40000000000)
  rootB := (1846202203/62500000000)
  rootU := (595302673687/1000000000000)
  rootV := (3247738561/200000000000)
  nonneg := by norm_num
  scalar := lowFrameWitness4_159.scalar_checked
  centre := fun n hn => lowFull4_159 hn
  energy_source := by
    intro n hn q hq hqu
    exact lowEnergy159 hn hq (by norm_num at hqu ⊢; exact hqu)
  enclosures := by
    intro n hn θ hθ
    exact lowFrameWitness4_159.bound (by norm_num) hn lowTIParameters159_valid (by norm_num)
      (le_trans (by norm_num) hθ.1) hθ.2 lowCorePair_cap lowCoreOutside_cap lowFrameBad_cap
      lowRotation2 lowRotation4 lowRotation12
noncomputable def lowRectangles4 (j : Fin 160) :
    FrameRectangleCertificate 10000 11000 (frameNoiseLower j) (frameNoiseUpper j) (lowTIParameters j) := by
  match j with
  | ⟨0,_⟩ => convert lowRectangle4_0 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨1,_⟩ => convert lowRectangle4_1 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨2,_⟩ => convert lowRectangle4_2 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨3,_⟩ => convert lowRectangle4_3 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨4,_⟩ => convert lowRectangle4_4 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨5,_⟩ => convert lowRectangle4_5 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨6,_⟩ => convert lowRectangle4_6 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨7,_⟩ => convert lowRectangle4_7 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨8,_⟩ => convert lowRectangle4_8 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨9,_⟩ => convert lowRectangle4_9 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨10,_⟩ => convert lowRectangle4_10 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨11,_⟩ => convert lowRectangle4_11 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨12,_⟩ => convert lowRectangle4_12 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨13,_⟩ => convert lowRectangle4_13 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨14,_⟩ => convert lowRectangle4_14 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨15,_⟩ => convert lowRectangle4_15 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨16,_⟩ => convert lowRectangle4_16 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨17,_⟩ => convert lowRectangle4_17 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨18,_⟩ => convert lowRectangle4_18 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨19,_⟩ => convert lowRectangle4_19 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨20,_⟩ => convert lowRectangle4_20 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨21,_⟩ => convert lowRectangle4_21 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨22,_⟩ => convert lowRectangle4_22 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨23,_⟩ => convert lowRectangle4_23 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨24,_⟩ => convert lowRectangle4_24 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨25,_⟩ => convert lowRectangle4_25 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨26,_⟩ => convert lowRectangle4_26 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨27,_⟩ => convert lowRectangle4_27 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨28,_⟩ => convert lowRectangle4_28 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨29,_⟩ => convert lowRectangle4_29 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨30,_⟩ => convert lowRectangle4_30 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨31,_⟩ => convert lowRectangle4_31 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨32,_⟩ => convert lowRectangle4_32 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨33,_⟩ => convert lowRectangle4_33 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨34,_⟩ => convert lowRectangle4_34 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨35,_⟩ => convert lowRectangle4_35 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨36,_⟩ => convert lowRectangle4_36 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨37,_⟩ => convert lowRectangle4_37 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨38,_⟩ => convert lowRectangle4_38 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨39,_⟩ => convert lowRectangle4_39 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨40,_⟩ => convert lowRectangle4_40 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨41,_⟩ => convert lowRectangle4_41 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨42,_⟩ => convert lowRectangle4_42 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨43,_⟩ => convert lowRectangle4_43 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨44,_⟩ => convert lowRectangle4_44 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨45,_⟩ => convert lowRectangle4_45 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨46,_⟩ => convert lowRectangle4_46 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨47,_⟩ => convert lowRectangle4_47 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨48,_⟩ => convert lowRectangle4_48 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨49,_⟩ => convert lowRectangle4_49 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨50,_⟩ => convert lowRectangle4_50 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨51,_⟩ => convert lowRectangle4_51 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨52,_⟩ => convert lowRectangle4_52 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨53,_⟩ => convert lowRectangle4_53 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨54,_⟩ => convert lowRectangle4_54 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨55,_⟩ => convert lowRectangle4_55 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨56,_⟩ => convert lowRectangle4_56 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨57,_⟩ => convert lowRectangle4_57 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨58,_⟩ => convert lowRectangle4_58 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨59,_⟩ => convert lowRectangle4_59 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨60,_⟩ => convert lowRectangle4_60 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨61,_⟩ => convert lowRectangle4_61 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨62,_⟩ => convert lowRectangle4_62 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨63,_⟩ => convert lowRectangle4_63 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨64,_⟩ => convert lowRectangle4_64 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨65,_⟩ => convert lowRectangle4_65 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨66,_⟩ => convert lowRectangle4_66 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨67,_⟩ => convert lowRectangle4_67 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨68,_⟩ => convert lowRectangle4_68 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨69,_⟩ => convert lowRectangle4_69 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨70,_⟩ => convert lowRectangle4_70 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨71,_⟩ => convert lowRectangle4_71 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨72,_⟩ => convert lowRectangle4_72 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨73,_⟩ => convert lowRectangle4_73 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨74,_⟩ => convert lowRectangle4_74 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨75,_⟩ => convert lowRectangle4_75 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨76,_⟩ => convert lowRectangle4_76 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨77,_⟩ => convert lowRectangle4_77 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨78,_⟩ => convert lowRectangle4_78 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨79,_⟩ => convert lowRectangle4_79 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨80,_⟩ => convert lowRectangle4_80 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨81,_⟩ => convert lowRectangle4_81 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨82,_⟩ => convert lowRectangle4_82 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨83,_⟩ => convert lowRectangle4_83 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨84,_⟩ => convert lowRectangle4_84 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨85,_⟩ => convert lowRectangle4_85 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨86,_⟩ => convert lowRectangle4_86 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨87,_⟩ => convert lowRectangle4_87 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨88,_⟩ => convert lowRectangle4_88 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨89,_⟩ => convert lowRectangle4_89 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨90,_⟩ => convert lowRectangle4_90 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨91,_⟩ => convert lowRectangle4_91 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨92,_⟩ => convert lowRectangle4_92 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨93,_⟩ => convert lowRectangle4_93 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨94,_⟩ => convert lowRectangle4_94 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨95,_⟩ => convert lowRectangle4_95 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨96,_⟩ => convert lowRectangle4_96 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨97,_⟩ => convert lowRectangle4_97 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨98,_⟩ => convert lowRectangle4_98 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨99,_⟩ => convert lowRectangle4_99 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨100,_⟩ => convert lowRectangle4_100 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨101,_⟩ => convert lowRectangle4_101 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨102,_⟩ => convert lowRectangle4_102 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨103,_⟩ => convert lowRectangle4_103 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨104,_⟩ => convert lowRectangle4_104 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨105,_⟩ => convert lowRectangle4_105 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨106,_⟩ => convert lowRectangle4_106 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨107,_⟩ => convert lowRectangle4_107 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨108,_⟩ => convert lowRectangle4_108 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨109,_⟩ => convert lowRectangle4_109 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨110,_⟩ => convert lowRectangle4_110 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨111,_⟩ => convert lowRectangle4_111 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨112,_⟩ => convert lowRectangle4_112 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨113,_⟩ => convert lowRectangle4_113 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨114,_⟩ => convert lowRectangle4_114 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨115,_⟩ => convert lowRectangle4_115 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨116,_⟩ => convert lowRectangle4_116 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨117,_⟩ => convert lowRectangle4_117 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨118,_⟩ => convert lowRectangle4_118 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨119,_⟩ => convert lowRectangle4_119 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨120,_⟩ => convert lowRectangle4_120 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨121,_⟩ => convert lowRectangle4_121 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨122,_⟩ => convert lowRectangle4_122 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨123,_⟩ => convert lowRectangle4_123 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨124,_⟩ => convert lowRectangle4_124 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨125,_⟩ => convert lowRectangle4_125 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨126,_⟩ => convert lowRectangle4_126 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨127,_⟩ => convert lowRectangle4_127 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨128,_⟩ => convert lowRectangle4_128 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨129,_⟩ => convert lowRectangle4_129 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨130,_⟩ => convert lowRectangle4_130 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨131,_⟩ => convert lowRectangle4_131 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨132,_⟩ => convert lowRectangle4_132 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨133,_⟩ => convert lowRectangle4_133 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨134,_⟩ => convert lowRectangle4_134 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨135,_⟩ => convert lowRectangle4_135 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨136,_⟩ => convert lowRectangle4_136 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨137,_⟩ => convert lowRectangle4_137 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨138,_⟩ => convert lowRectangle4_138 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨139,_⟩ => convert lowRectangle4_139 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨140,_⟩ => convert lowRectangle4_140 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨141,_⟩ => convert lowRectangle4_141 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨142,_⟩ => convert lowRectangle4_142 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨143,_⟩ => convert lowRectangle4_143 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨144,_⟩ => convert lowRectangle4_144 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨145,_⟩ => convert lowRectangle4_145 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨146,_⟩ => convert lowRectangle4_146 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨147,_⟩ => convert lowRectangle4_147 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨148,_⟩ => convert lowRectangle4_148 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨149,_⟩ => convert lowRectangle4_149 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨150,_⟩ => convert lowRectangle4_150 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨151,_⟩ => convert lowRectangle4_151 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨152,_⟩ => convert lowRectangle4_152 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨153,_⟩ => convert lowRectangle4_153 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨154,_⟩ => convert lowRectangle4_154 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨155,_⟩ => convert lowRectangle4_155 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨156,_⟩ => convert lowRectangle4_156 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨157,_⟩ => convert lowRectangle4_157 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨158,_⟩ => convert lowRectangle4_158 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨159,_⟩ => convert lowRectangle4_159 using 1 <;> norm_num [frameNoiseLower,frameNoiseUpper,lowTIParameters,lowTIParametersBatch0,lowTIParametersBatch1,lowTIParametersBatch2,lowTIParametersBatch3,lowTIParametersBatch4,lowTIParametersBatch5,lowTIParametersBatch6,lowTIParametersBatch7,lowTIParametersBatch8,lowTIParametersBatch9]
  | ⟨j+160,h⟩ => exact False.elim (by omega)
end BstLean.BlueprintLow
