import BstLean.Part255Events
import BstLean.Part254GaussianScalar
namespace BstLean.Part255
open Real Set BstLean.Part182

theorem lambda_bound {a b c L : ℝ} (h0 : 0 ≤ L - (a+c)/2)
    (h1 : ((a-c)/2)^2+b^2 ≤ (L-(a+c)/2)^2) : ta_lam a b c ≤ L := by
  have h := (Real.sqrt_le_left h0).mpr h1
  unfold ta_lam
  linarith

noncomputable def parameters : Fin 43 → Parameters
  | ⟨0, _⟩ => ⟨(50083597 / 125000000), (6825149 / 10000000), (58106111 / 125000000), (596791377 / 1000000000), (311219 / 500000), (111473 / 500000), (71709 / 125000), (141923 / 1000000), (33751 / 1000000), (31263469 / 50000000), (576294479 / 1000000000), (471811289 / 1000000000), (92528399984147741 / 1000000000000000000), (12189344701157853 / 250000000000000000)⟩
  | ⟨1, _⟩ => ⟨(199723729 / 500000000), (340691301 / 500000000), (231820643 / 500000000), (595611421 / 1000000000), (621741 / 1000000), (2771 / 12500), (11461 / 20000), (14243 / 100000), (33751 / 1000000), (624568409 / 1000000000), (71959909 / 125000000), (470854519 / 1000000000), (46316204527319579 / 500000000000000000), (24410026977526763 / 500000000000000000)⟩
  | ⟨2, _⟩ => ⟨(398226781 / 1000000000), (136049893 / 200000000), (92486807 / 200000000), (118886213 / 200000000), (310523 / 500000), (220417 / 1000000), (572429 / 1000000), (17867 / 125000), (33751 / 1000000), (38991841 / 62500000), (1123174 / 1953125), (18795941 / 40000000), (92736104933326719 / 1000000000000000000), (48882582949300507 / 1000000000000000000)⟩
  | ⟨3, _⟩ => ⟨(79401349 / 200000000), (679115489 / 1000000000), (3603337 / 7812500), (593250309 / 1000000000), (9693 / 15625), (54789 / 250000), (571809 / 1000000), (1793 / 12500), (33751 / 1000000), (623171521 / 1000000000), (7180649 / 12500000), (234471647 / 500000000), (23209871933911427 / 250000000000000000), (9788993168248431 / 200000000000000000)⟩
  | ⟨4, _⟩ => ⟨(395787347 / 1000000000), (677980677 / 1000000000), (230010293 / 500000000), (592069153 / 1000000000), (619659 / 1000000), (217897 / 1000000), (57119 / 100000), (143943 / 1000000), (33751 / 1000000), (155618651 / 250000000), (17932493 / 31250000), (29249301 / 62500000), (92942557571560933 / 1000000000000000000), (49007202682195379 / 1000000000000000000)⟩
  | ⟨5, _⟩ => ⟨(197284293 / 500000000), (676845029 / 1000000000), (229407193 / 500000000), (590887599 / 1000000000), (618967 / 1000000), (216641 / 1000000), (142643 / 250000), (36111 / 250000), (33751 / 1000000), (621778711 / 1000000000), (573228649 / 1000000000), (467035077 / 1000000000), (46522657272786153 / 500000000000000000), (24534646760463403 / 500000000000000000)⟩
  | ⟨6, _⟩ => ⟨(393350461 / 1000000000), (337854273 / 500000000), (228804267 / 500000000), (589705647 / 1000000000), (154569 / 250000), (215387 / 1000000), (284977 / 500000), (9059 / 62500), (33751 / 1000000), (155270959 / 250000000), (572617551 / 1000000000), (233041033 / 500000000), (93147758756723879 / 1000000000000000000), (49131238403656993 / 1000000000000000000)⟩
  | ⟨7, _⟩ => ⟨(392132971 / 1000000000), (674571229 / 1000000000), (456403031 / 1000000000), (588523297 / 1000000000), (308793 / 500000), (26767 / 125000), (284669 / 500000), (72721 / 500000), (33751 / 1000000), (124077997 / 200000000), (35750529 / 62500000), (465129773 / 1000000000), (5828118143663443 / 62500000000000000), (1967721494962627 / 40000000000000000)⟩
  | ⟨8, _⟩ => ⟨(195458057 / 500000000), (673433079 / 1000000000), (113799469 / 250000000), (11746811 / 20000000), (616897 / 1000000), (26611 / 125000), (568723 / 1000000), (145939 / 1000000), (33751 / 1000000), (619697159 / 1000000000), (1428501 / 2500000), (92835637 / 200000000), (93351709259408889 / 1000000000000000000), (3078418154580973 / 62500000000000000)⟩
  | ⟨9, _⟩ => ⟨(389699889 / 1000000000), (336147049 / 500000000), (113498267 / 250000000), (586157407 / 1000000000), (616209 / 1000000), (211641 / 1000000), (568109 / 1000000), (29287 / 200000), (33751 / 1000000), (309502671 / 500000000), (570793359 / 1000000000), (46322729 / 100000000), (93453215721836713 / 1000000000000000000), (49316197739954673 / 1000000000000000000)⟩
  | ⟨10, _⟩ => ⟨(77696859 / 200000000), (335577143 / 500000000), (226394303 / 500000000), (584973867 / 1000000000), (307761 / 500000), (105199 / 500000), (70937 / 125000), (146929 / 1000000), (33751 / 1000000), (618314557 / 1000000000), (71273417 / 125000000), (231138539 / 500000000), (9355440976320561 / 100000000000000000), (49377559210119611 / 1000000000000000000)⟩
  | ⟨11, _⟩ => ⟨(38726933 / 100000000), (134002729 / 200000000), (45158449 / 100000000), (145947483 / 250000000), (153709 / 250000), (52289 / 250000), (566883 / 1000000), (73711 / 500000), (33751 / 1000000), (308812391 / 500000000), (284790671 / 500000000), (461327537 / 1000000000), (18731058291081787 / 200000000000000000), (9887754983468123 / 200000000000000000)⟩
  | ⟨12, _⟩ => ⟨(386054993 / 1000000000), (26754887 / 40000000), (450380719 / 1000000000), (291302801 / 500000000), (76769 / 125000), (207917 / 1000000), (8848 / 15625), (147913 / 1000000), (33751 / 1000000), (616937023 / 1000000000), (568977359 / 1000000000), (460378657 / 1000000000), (2343896521623181 / 25000000000000000), (6187480611580243 / 125000000000000000)⟩
  | ⟨13, _⟩ => ⟨(192420641 / 500000000), (667729877 / 1000000000), (112294323 / 250000000), (290710439 / 500000000), (153367 / 250000), (206681 / 1000000), (565661 / 1000000), (148403 / 1000000), (33751 / 1000000), (123249859 / 200000000), (284186703 / 500000000), (18377217 / 40000000), (93856118052839337 / 1000000000000000000), (24780384582263521 / 500000000000000000)⟩
  | ⟨14, _⟩ => ⟨(383628197 / 1000000000), (666586753 / 1000000000), (44797421 / 100000000), (7252947 / 12500000), (122557 / 200000), (205447 / 1000000), (141263 / 250000), (149019 / 1000000), (33751 / 1000000), (615562583 / 1000000000), (56777229 / 100000000), (458482831 / 1000000000), (46978031537411791 / 500000000000000000), (24810773879489571 / 500000000000000000)⟩
  | ⟨15, _⟩ => ⟨(47801967 / 125000000), (166360701 / 250000000), (446771471 / 1000000000), (72381281 / 125000000), (612103 / 1000000), (40843 / 200000), (564443 / 1000000), (74869 / 500000), (33751 / 1000000), (76859611 / 125000000), (35448243 / 62500000), (57191983 / 125000000), (94055695981162651 / 1000000000000000000), (49682180699463493 / 1000000000000000000)⟩
  | ⟨16, _⟩ => ⟨(190601949 / 500000000), (66429803 / 100000000), (17822763 / 40000000), (577864343 / 1000000000), (305711 / 500000), (101493 / 500000), (112767 / 200000), (75227 / 500000), (33751 / 1000000), (76774027 / 125000000), (283286257 / 500000000), (456589513 / 1000000000), (4707750840837531 / 50000000000000000), (6217833500866333 / 125000000000000000)⟩
  | ⟨17, _⟩ => ⟨(189996341 / 500000000), (41447027 / 62500000), (444367021 / 1000000000), (288339023 / 500000000), (610743 / 1000000), (1261 / 6250), (140807 / 250000), (2362 / 15625), (33751 / 1000000), (613509561 / 1000000000), (22638967 / 40000000), (455643767 / 1000000000), (94254025621098029 / 1000000000000000000), (12450752424954727 / 250000000000000000)⟩
  | ⟨18, _⟩ => ⟨(75756417 / 200000000), (165501503 / 250000000), (443165309 / 1000000000), (575491357 / 1000000000), (38129 / 62500), (40107 / 200000), (281311 / 500000), (151879 / 1000000), (33751 / 1000000), (612826921 / 1000000000), (17668027 / 31250000), (56837327 / 125000000), (47176361214163061 / 500000000000000000), (49863205794051471 / 1000000000000000000)⟩
  | ⟨19, _⟩ => ⟨(94393027 / 250000000), (66085877 / 100000000), (220981969 / 500000000), (574304277 / 1000000000), (304693 / 500000), (199313 / 1000000), (562017 / 1000000), (38147 / 250000), (33751 / 1000000), (122429061 / 200000000), (564780587 / 1000000000), (7089907 / 15625000), (94451107267184319 / 1000000000000000000), (49923256303044749 / 1000000000000000000)⟩
  | ⟨20, _⟩ => ⟨(376362749 / 1000000000), (659710707 / 1000000000), (440762907 / 1000000000), (286558403 / 500000000), (608709 / 1000000), (99047 / 500000), (561413 / 1000000), (76647 / 500000), (33751 / 1000000), (611464711 / 1000000000), (564185339 / 1000000000), (226405027 / 500000000), (2363729504025953 / 25000000000000000), (24991580618851321 / 500000000000000000)⟩
  | ⟨21, _⟩ => ⟨(375154007 / 1000000000), (26342473 / 40000000), (439562217 / 1000000000), (35745559 / 62500000), (304017 / 500000), (196877 / 1000000), (56081 / 100000), (76999 / 500000), (33751 / 1000000), (305393063 / 500000000), (281795563 / 500000000), (225933311 / 500000000), (94646941127880397 / 1000000000000000000), (781920634475341 / 15625000000000000)⟩
  | ⟨22, _⟩ => ⟨(9348647 / 25000000), (164353031 / 250000000), (87672373 / 200000000), (142685173 / 250000000), (607359 / 1000000), (97831 / 500000), (35013 / 62500), (154699 / 1000000), (33751 / 1000000), (152526891 / 250000000), (281498971 / 500000000), (450923743 / 1000000000), (47372195090165799 / 500000000000000000), (50102534415091837 / 1000000000000000000)⟩
  | ⟨23, _⟩ => ⟨(372738367 / 1000000000), (328130803 / 500000000), (437161853 / 1000000000), (569552051 / 1000000000), (121337 / 200000), (194449 / 1000000), (279803 / 500000), (77699 / 500000), (33751 / 1000000), (304715009 / 500000000), (562404799 / 1000000000), (89996281 / 200000000), (94841527325638223 / 1000000000000000000), (2508100133354719 / 50000000000000000)⟩
  | ⟨24, _⟩ => ⟨(371531467 / 1000000000), (65511027 / 100000000), (217981089 / 500000000), (568363021 / 1000000000), (151503 / 250000), (193239 / 1000000), (279503 / 500000), (31219 / 200000), (33751 / 1000000), (608753493 / 1000000000), (112362737 / 200000000), (224519799 / 500000000), (23734588141418359 / 250000000000000000), (50221325363303599 / 1000000000000000000)⟩
  | ⟨25, _⟩ => ⟨(370325179 / 1000000000), (653958119 / 1000000000), (217381421 / 500000000), (567173603 / 1000000000), (30267 / 50000), (193769 / 1000000), (279203 / 500000), (156789 / 1000000), (33751 / 1000000), (304044697 / 500000000), (280611303 / 500000000), (448098313 / 1000000000), (23758716474234959 / 250000000000000000), (12570125625521843 / 250000000000000000)⟩
  | ⟨26, _⟩ => ⟨(184559751 / 500000000), (652805153 / 1000000000), (216781921 / 500000000), (141495949 / 250000000), (604669 / 1000000), (12147 / 62500), (34863 / 62500), (3937 / 25000), (33751 / 1000000), (303713343 / 500000000), (560633549 / 1000000000), (223578769 / 500000000), (95131067310570541 / 1000000000000000000), (50339534079307821 / 1000000000000000000)⟩
  | ⟨27, _⟩ => ⟨(183957217 / 500000000), (162912843 / 250000000), (21618259 / 50000000), (282396801 / 500000000), (603999 / 1000000), (194931 / 1000000), (55721 / 100000), (158169 / 1000000), (33751 / 1000000), (303382497 / 500000000), (112008907 / 200000000), (89243453 / 200000000), (47613478396159551 / 500000000000000000), (25199210044158301 / 500000000000000000)⟩
  | ⟨28, _⟩ => ⟨(183354987 / 500000000), (325248389 / 500000000), (431166853 / 1000000000), (28180151 / 50000000), (60333 / 100000), (195509 / 1000000), (556613 / 1000000), (19857 / 125000), (33751 / 1000000), (303052169 / 500000000), (139864139 / 250000000), (222638741 / 500000000), (95322534322572899 / 1000000000000000000), (1261429012999029 / 25000000000000000)⟩
  | ⟨29, _⟩ => ⟨(182753061 / 500000000), (162335343 / 250000000), (214984431 / 500000000), (140603013 / 250000000), (301331 / 500000), (49021 / 250000), (556017 / 1000000), (7977 / 50000), (33751 / 1000000), (121088941 / 200000000), (279434803 / 500000000), (444338179 / 1000000000), (4770889993816841 / 50000000000000000), (50515755362577109 / 1000000000000000000)⟩
  | ⟨30, _⟩ => ⟨(2914423 / 8000000), (129637031 / 200000000), (85754241 / 200000000), (280610349 / 500000000), (120399 / 200000), (98329 / 500000), (555421 / 1000000), (80111 / 500000), (33751 / 1000000), (604786109 / 1000000000), (5582827 / 10000000), (443399347 / 1000000000), (95512753423240401 / 1000000000000000000), (25287102300995783 / 500000000000000000)⟩
  | ⟨31, _⟩ => ⟨(181550117 / 500000000), (647028127 / 1000000000), (106893471 / 250000000), (280014479 / 500000000), (601329 / 1000000), (49307 / 250000), (554827 / 1000000), (160901 / 1000000), (33751 / 1000000), (60412853 / 100000000), (111539563 / 200000000), (442460977 / 1000000000), (1912147898550679 / 20000000000000000), (50632508221521341 / 1000000000000000000)⟩
  | ⟨32, _⟩ => ⟨(90474549 / 250000000), (64587029 / 100000000), (6662139 / 15625000), (17463651 / 31250000), (75083 / 125000), (197797 / 1000000), (277117 / 500000), (80789 / 500000), (33751 / 1000000), (603471987 / 1000000000), (278556983 / 500000000), (27595191 / 62500000), (95701724348082691 / 1000000000000000000), (25345333100985103 / 500000000000000000)⟩
  | ⟨33, _⟩ => ⟨(360696761 / 1000000000), (644711643 / 1000000000), (425180241 / 1000000000), (278822161 / 500000000), (599999 / 1000000), (198363 / 1000000), (553641 / 1000000), (162253 / 1000000), (33751 / 1000000), (24112619 / 40000000), (556530161 / 1000000000), (220292789 / 500000000), (2394893540959083 / 25000000000000000), (25374339260813643 / 500000000000000000)⟩
  | ⟨34, _⟩ => ⟨(359495927 / 1000000000), (643552189 / 1000000000), (5299799 / 12500000), (556451427 / 1000000000), (74917 / 125000), (12433 / 62500), (553049 / 1000000), (6517 / 40000), (33751 / 1000000), (602160993 / 1000000000), (111189477 / 200000000), (43964853 / 100000000), (19177889349292789 / 200000000000000000), (5080654515626703 / 100000000000000000)⟩
  | ⟨35, _⟩ => ⟨(358295693 / 1000000000), (80298991 / 125000000), (42278793 / 100000000), (138814537 / 250000000), (299337 / 500000), (19949 / 100000), (276229 / 500000), (32719 / 200000), (33751 / 1000000), (300753767 / 500000000), (277682823 / 500000000), (13709747 / 31250000), (9598283961507427 / 100000000000000000), (10172853215828927 / 200000000000000000)⟩
  | ⟨36, _⟩ => ⟨(357096059 / 1000000000), (32061543 / 50000000), (421592273 / 1000000000), (277032243 / 500000000), (149503 / 250000), (200049 / 1000000), (137967 / 250000), (82131 / 500000), (33751 / 1000000), (120170821 / 200000000), (110956987 / 200000000), (437775691 / 1000000000), (96075920181486003 / 1000000000000000000), (50921841260996229 / 1000000000000000000)⟩
  | ⟨37, _⟩ => ⟨(355897023 / 1000000000), (640068987 / 1000000000), (420396947 / 1000000000), (552870441 / 1000000000), (74669 / 125000), (200607 / 1000000), (551279 / 1000000), (164927 / 1000000), (33751 / 1000000), (600202707 / 1000000000), (277102631 / 500000000), (436839879 / 1000000000), (37565893897493 / 390625000000000), (50979270670033851 / 1000000000000000000)⟩
  | ⟨38, _⟩ => ⟨(44337323 / 125000000), (63890631 / 100000000), (13100061 / 31250000), (137919003 / 250000000), (149173 / 250000), (201163 / 1000000), (550691 / 1000000), (16559 / 100000), (33751 / 1000000), (299775673 / 500000000), (4429013 / 8000000), (435904461 / 1000000000), (96261144129836149 / 1000000000000000000), (25518277135972601 / 500000000000000000)⟩
  | ⟨39, _⟩ => ⟨(353500741 / 1000000000), (159435707 / 250000000), (418007287 / 1000000000), (275240601 / 500000000), (596033 / 1000000), (50429 / 250000), (550103 / 1000000), (166251 / 1000000), (33751 / 1000000), (598901009 / 1000000000), (553048033 / 1000000000), (434969427 / 1000000000), (9635328735930219 / 100000000000000000), (51093692029888807 / 1000000000000000000)⟩
  | ⟨40, _⟩ => ⟨(352303493 / 1000000000), (39786159 / 62500000), (52101619 / 125000000), (54928601 / 100000000), (4763 / 8000), (202267 / 1000000), (137379 / 250000), (166909 / 1000000), (33751 / 1000000), (598251703 / 1000000000), (552470471 / 1000000000), (217017383 / 500000000), (96445117981607711 / 1000000000000000000), (12787670976122709 / 250000000000000000)⟩
  | ⟨41, _⟩ => ⟨(351106839 / 1000000000), (317706729 / 500000000), (207809473 / 500000000), (137022609 / 250000000), (297359 / 500000), (3169 / 15625), (54893 / 100000), (33513 / 200000), (33751 / 1000000), (597603427 / 1000000000), (275946973 / 500000000), (433100471 / 1000000000), (96536635906950411 / 1000000000000000000), (1024150597076871 / 20000000000000000)⟩
  | ⟨42, _⟩ => ⟨(349910777 / 1000000000), (63424757 / 100000000), (414425269 / 1000000000), (546894481 / 1000000000), (297031 / 500000), (203363 / 1000000), (109669 / 200000), (84109 / 500000), (33751 / 1000000), (298478091 / 500000000), (11026369 / 20000000), (432166531 / 1000000000), (24156960260021279 / 250000000000000000), (25632114916749599 / 500000000000000000)⟩
  | ⟨j + 43, h⟩ => False.elim (by omega)

theorem valid0 : Valid (parameters ⟨0, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid1 : Valid (parameters ⟨1, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid2 : Valid (parameters ⟨2, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid3 : Valid (parameters ⟨3, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid4 : Valid (parameters ⟨4, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid5 : Valid (parameters ⟨5, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid6 : Valid (parameters ⟨6, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid7 : Valid (parameters ⟨7, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid8 : Valid (parameters ⟨8, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid9 : Valid (parameters ⟨9, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid10 : Valid (parameters ⟨10, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid11 : Valid (parameters ⟨11, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid12 : Valid (parameters ⟨12, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid13 : Valid (parameters ⟨13, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid14 : Valid (parameters ⟨14, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid15 : Valid (parameters ⟨15, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid16 : Valid (parameters ⟨16, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid17 : Valid (parameters ⟨17, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid18 : Valid (parameters ⟨18, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid19 : Valid (parameters ⟨19, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid20 : Valid (parameters ⟨20, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid21 : Valid (parameters ⟨21, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid22 : Valid (parameters ⟨22, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid23 : Valid (parameters ⟨23, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid24 : Valid (parameters ⟨24, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid25 : Valid (parameters ⟨25, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid26 : Valid (parameters ⟨26, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid27 : Valid (parameters ⟨27, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid28 : Valid (parameters ⟨28, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid29 : Valid (parameters ⟨29, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid30 : Valid (parameters ⟨30, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid31 : Valid (parameters ⟨31, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid32 : Valid (parameters ⟨32, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid33 : Valid (parameters ⟨33, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid34 : Valid (parameters ⟨34, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid35 : Valid (parameters ⟨35, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid36 : Valid (parameters ⟨36, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid37 : Valid (parameters ⟨37, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid38 : Valid (parameters ⟨38, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid39 : Valid (parameters ⟨39, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid40 : Valid (parameters ⟨40, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid41 : Valid (parameters ⟨41, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem valid42 : Valid (parameters ⟨42, by decide⟩) := by
  constructor
  all_goals first
    | (apply lambda_bound <;> norm_num [parameters])
    | norm_num [parameters]

theorem parameters_valid (j : Fin 43) : Valid (parameters j) := by
  match j with
  | ⟨0, _⟩ => exact valid0
  | ⟨1, _⟩ => exact valid1
  | ⟨2, _⟩ => exact valid2
  | ⟨3, _⟩ => exact valid3
  | ⟨4, _⟩ => exact valid4
  | ⟨5, _⟩ => exact valid5
  | ⟨6, _⟩ => exact valid6
  | ⟨7, _⟩ => exact valid7
  | ⟨8, _⟩ => exact valid8
  | ⟨9, _⟩ => exact valid9
  | ⟨10, _⟩ => exact valid10
  | ⟨11, _⟩ => exact valid11
  | ⟨12, _⟩ => exact valid12
  | ⟨13, _⟩ => exact valid13
  | ⟨14, _⟩ => exact valid14
  | ⟨15, _⟩ => exact valid15
  | ⟨16, _⟩ => exact valid16
  | ⟨17, _⟩ => exact valid17
  | ⟨18, _⟩ => exact valid18
  | ⟨19, _⟩ => exact valid19
  | ⟨20, _⟩ => exact valid20
  | ⟨21, _⟩ => exact valid21
  | ⟨22, _⟩ => exact valid22
  | ⟨23, _⟩ => exact valid23
  | ⟨24, _⟩ => exact valid24
  | ⟨25, _⟩ => exact valid25
  | ⟨26, _⟩ => exact valid26
  | ⟨27, _⟩ => exact valid27
  | ⟨28, _⟩ => exact valid28
  | ⟨29, _⟩ => exact valid29
  | ⟨30, _⟩ => exact valid30
  | ⟨31, _⟩ => exact valid31
  | ⟨32, _⟩ => exact valid32
  | ⟨33, _⟩ => exact valid33
  | ⟨34, _⟩ => exact valid34
  | ⟨35, _⟩ => exact valid35
  | ⟨36, _⟩ => exact valid36
  | ⟨37, _⟩ => exact valid37
  | ⟨38, _⟩ => exact valid38
  | ⟨39, _⟩ => exact valid39
  | ⟨40, _⟩ => exact valid40
  | ⟨41, _⟩ => exact valid41
  | ⟨42, _⟩ => exact valid42
  | ⟨j + 43, h⟩ => exact False.elim (by omega)

noncomputable def envelope (p : Parameters) (θ : ℝ) : ℝ :=
  θ * (p.cLam / (1 - 4 * θ / 12225) +
    p.wLam / (1 - p.cRadius) * (1374279 / 10^9) +
    p.wLam / (1 - p.wRadius) * (6216465741 / 10^12)) +
    (13/10) * (58249 / 10^8)

noncomputable def localCap : Fin 43 → ℝ
  | ⟨0, _⟩ => (137976367 / 500000000)
  | ⟨1, _⟩ => (138178003 / 500000000)
  | ⟨2, _⟩ => (276758283 / 1000000000)
  | ⟨3, _⟩ => (277159561 / 1000000000)
  | ⟨4, _⟩ => (277559849 / 1000000000)
  | ⟨5, _⟩ => (55591829 / 200000000)
  | ⟨6, _⟩ => (13917849 / 50000000)
  | ⟨7, _⟩ => (69688577 / 250000000)
  | ⟨8, _⟩ => (279150659 / 1000000000)
  | ⟨9, _⟩ => (279546037 / 1000000000)
  | ⟨10, _⟩ => (279940443 / 1000000000)
  | ⟨11, _⟩ => (280333399 / 1000000000)
  | ⟨12, _⟩ => (140362939 / 500000000)
  | ⟨13, _⟩ => (70279227 / 250000000)
  | ⟨14, _⟩ => (28150787 / 100000000)
  | ⟨15, _⟩ => (70474433 / 250000000)
  | ⟨16, _⟩ => (5645733 / 20000000)
  | ⟨17, _⟩ => (70668659 / 250000000)
  | ⟨18, _⟩ => (141530841 / 500000000)
  | ⟨19, _⟩ => (141723899 / 500000000)
  | ⟨20, _⟩ => (283832987 / 1000000000)
  | ⟨21, _⟩ => (142108629 / 500000000)
  | ⟨22, _⟩ => (71150151 / 250000000)
  | ⟨23, _⟩ => (284982539 / 1000000000)
  | ⟨24, _⟩ => (14268203 / 50000000)
  | ⟨25, _⟩ => (285744219 / 1000000000)
  | ⟨26, _⟩ => (286123973 / 1000000000)
  | ⟨27, _⟩ => (286502327 / 1000000000)
  | ⟨28, _⟩ => (286879783 / 1000000000)
  | ⟨29, _⟩ => (287256343 / 1000000000)
  | ⟨30, _⟩ => (71907877 / 250000000)
  | ⟨31, _⟩ => (18000393 / 62500000)
  | ⟨32, _⟩ => (144190093 / 500000000)
  | ⟨33, _⟩ => (144376347 / 500000000)
  | ⟨34, _⟩ => (11564973 / 40000000)
  | ⟨35, _⟩ => (72373771 / 250000000)
  | ⟨36, _⟩ => (57972993 / 200000000)
  | ⟨37, _⟩ => (145116993 / 500000000)
  | ⟨38, _⟩ => (290602141 / 1000000000)
  | ⟨39, _⟩ => (290968923 / 1000000000)
  | ⟨40, _⟩ => (58266969 / 200000000)
  | ⟨41, _⟩ => (58339983 / 200000000)
  | ⟨42, _⟩ => (291823659 / 1000000000)
  | ⟨j + 43, h⟩ => False.elim (by omega)

theorem localCap_mono : Monotone localCap := by
  apply Fin.monotone_iff_le_succ.mpr
  intro j
  fin_cases j <;> norm_num [localCap]

theorem grid0 :
    envelope (parameters ⟨0, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨0, by decide⟩)) ≤ localCap ⟨0, by decide⟩ ∧
    localCap ⟨0, by decide⟩ - 1/10^9 < envelope (parameters ⟨0, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨0, by decide⟩)) ∧
    0 ≤ localCap ⟨0, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid1 :
    envelope (parameters ⟨1, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨1, by decide⟩)) ≤ localCap ⟨1, by decide⟩ ∧
    localCap ⟨1, by decide⟩ - 1/10^9 < envelope (parameters ⟨1, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨1, by decide⟩)) ∧
    0 ≤ localCap ⟨1, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid2 :
    envelope (parameters ⟨2, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨2, by decide⟩)) ≤ localCap ⟨2, by decide⟩ ∧
    localCap ⟨2, by decide⟩ - 1/10^9 < envelope (parameters ⟨2, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨2, by decide⟩)) ∧
    0 ≤ localCap ⟨2, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid3 :
    envelope (parameters ⟨3, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨3, by decide⟩)) ≤ localCap ⟨3, by decide⟩ ∧
    localCap ⟨3, by decide⟩ - 1/10^9 < envelope (parameters ⟨3, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨3, by decide⟩)) ∧
    0 ≤ localCap ⟨3, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid4 :
    envelope (parameters ⟨4, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨4, by decide⟩)) ≤ localCap ⟨4, by decide⟩ ∧
    localCap ⟨4, by decide⟩ - 1/10^9 < envelope (parameters ⟨4, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨4, by decide⟩)) ∧
    0 ≤ localCap ⟨4, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid5 :
    envelope (parameters ⟨5, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨5, by decide⟩)) ≤ localCap ⟨5, by decide⟩ ∧
    localCap ⟨5, by decide⟩ - 1/10^9 < envelope (parameters ⟨5, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨5, by decide⟩)) ∧
    0 ≤ localCap ⟨5, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid6 :
    envelope (parameters ⟨6, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨6, by decide⟩)) ≤ localCap ⟨6, by decide⟩ ∧
    localCap ⟨6, by decide⟩ - 1/10^9 < envelope (parameters ⟨6, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨6, by decide⟩)) ∧
    0 ≤ localCap ⟨6, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid7 :
    envelope (parameters ⟨7, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨7, by decide⟩)) ≤ localCap ⟨7, by decide⟩ ∧
    localCap ⟨7, by decide⟩ - 1/10^9 < envelope (parameters ⟨7, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨7, by decide⟩)) ∧
    0 ≤ localCap ⟨7, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid8 :
    envelope (parameters ⟨8, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨8, by decide⟩)) ≤ localCap ⟨8, by decide⟩ ∧
    localCap ⟨8, by decide⟩ - 1/10^9 < envelope (parameters ⟨8, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨8, by decide⟩)) ∧
    0 ≤ localCap ⟨8, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid9 :
    envelope (parameters ⟨9, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨9, by decide⟩)) ≤ localCap ⟨9, by decide⟩ ∧
    localCap ⟨9, by decide⟩ - 1/10^9 < envelope (parameters ⟨9, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨9, by decide⟩)) ∧
    0 ≤ localCap ⟨9, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid10 :
    envelope (parameters ⟨10, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨10, by decide⟩)) ≤ localCap ⟨10, by decide⟩ ∧
    localCap ⟨10, by decide⟩ - 1/10^9 < envelope (parameters ⟨10, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨10, by decide⟩)) ∧
    0 ≤ localCap ⟨10, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid11 :
    envelope (parameters ⟨11, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨11, by decide⟩)) ≤ localCap ⟨11, by decide⟩ ∧
    localCap ⟨11, by decide⟩ - 1/10^9 < envelope (parameters ⟨11, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨11, by decide⟩)) ∧
    0 ≤ localCap ⟨11, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid12 :
    envelope (parameters ⟨12, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨12, by decide⟩)) ≤ localCap ⟨12, by decide⟩ ∧
    localCap ⟨12, by decide⟩ - 1/10^9 < envelope (parameters ⟨12, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨12, by decide⟩)) ∧
    0 ≤ localCap ⟨12, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid13 :
    envelope (parameters ⟨13, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨13, by decide⟩)) ≤ localCap ⟨13, by decide⟩ ∧
    localCap ⟨13, by decide⟩ - 1/10^9 < envelope (parameters ⟨13, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨13, by decide⟩)) ∧
    0 ≤ localCap ⟨13, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid14 :
    envelope (parameters ⟨14, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨14, by decide⟩)) ≤ localCap ⟨14, by decide⟩ ∧
    localCap ⟨14, by decide⟩ - 1/10^9 < envelope (parameters ⟨14, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨14, by decide⟩)) ∧
    0 ≤ localCap ⟨14, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid15 :
    envelope (parameters ⟨15, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨15, by decide⟩)) ≤ localCap ⟨15, by decide⟩ ∧
    localCap ⟨15, by decide⟩ - 1/10^9 < envelope (parameters ⟨15, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨15, by decide⟩)) ∧
    0 ≤ localCap ⟨15, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid16 :
    envelope (parameters ⟨16, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨16, by decide⟩)) ≤ localCap ⟨16, by decide⟩ ∧
    localCap ⟨16, by decide⟩ - 1/10^9 < envelope (parameters ⟨16, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨16, by decide⟩)) ∧
    0 ≤ localCap ⟨16, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid17 :
    envelope (parameters ⟨17, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨17, by decide⟩)) ≤ localCap ⟨17, by decide⟩ ∧
    localCap ⟨17, by decide⟩ - 1/10^9 < envelope (parameters ⟨17, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨17, by decide⟩)) ∧
    0 ≤ localCap ⟨17, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid18 :
    envelope (parameters ⟨18, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨18, by decide⟩)) ≤ localCap ⟨18, by decide⟩ ∧
    localCap ⟨18, by decide⟩ - 1/10^9 < envelope (parameters ⟨18, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨18, by decide⟩)) ∧
    0 ≤ localCap ⟨18, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid19 :
    envelope (parameters ⟨19, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨19, by decide⟩)) ≤ localCap ⟨19, by decide⟩ ∧
    localCap ⟨19, by decide⟩ - 1/10^9 < envelope (parameters ⟨19, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨19, by decide⟩)) ∧
    0 ≤ localCap ⟨19, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid20 :
    envelope (parameters ⟨20, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨20, by decide⟩)) ≤ localCap ⟨20, by decide⟩ ∧
    localCap ⟨20, by decide⟩ - 1/10^9 < envelope (parameters ⟨20, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨20, by decide⟩)) ∧
    0 ≤ localCap ⟨20, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid21 :
    envelope (parameters ⟨21, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨21, by decide⟩)) ≤ localCap ⟨21, by decide⟩ ∧
    localCap ⟨21, by decide⟩ - 1/10^9 < envelope (parameters ⟨21, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨21, by decide⟩)) ∧
    0 ≤ localCap ⟨21, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid22 :
    envelope (parameters ⟨22, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨22, by decide⟩)) ≤ localCap ⟨22, by decide⟩ ∧
    localCap ⟨22, by decide⟩ - 1/10^9 < envelope (parameters ⟨22, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨22, by decide⟩)) ∧
    0 ≤ localCap ⟨22, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid23 :
    envelope (parameters ⟨23, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨23, by decide⟩)) ≤ localCap ⟨23, by decide⟩ ∧
    localCap ⟨23, by decide⟩ - 1/10^9 < envelope (parameters ⟨23, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨23, by decide⟩)) ∧
    0 ≤ localCap ⟨23, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid24 :
    envelope (parameters ⟨24, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨24, by decide⟩)) ≤ localCap ⟨24, by decide⟩ ∧
    localCap ⟨24, by decide⟩ - 1/10^9 < envelope (parameters ⟨24, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨24, by decide⟩)) ∧
    0 ≤ localCap ⟨24, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid25 :
    envelope (parameters ⟨25, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨25, by decide⟩)) ≤ localCap ⟨25, by decide⟩ ∧
    localCap ⟨25, by decide⟩ - 1/10^9 < envelope (parameters ⟨25, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨25, by decide⟩)) ∧
    0 ≤ localCap ⟨25, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid26 :
    envelope (parameters ⟨26, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨26, by decide⟩)) ≤ localCap ⟨26, by decide⟩ ∧
    localCap ⟨26, by decide⟩ - 1/10^9 < envelope (parameters ⟨26, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨26, by decide⟩)) ∧
    0 ≤ localCap ⟨26, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid27 :
    envelope (parameters ⟨27, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨27, by decide⟩)) ≤ localCap ⟨27, by decide⟩ ∧
    localCap ⟨27, by decide⟩ - 1/10^9 < envelope (parameters ⟨27, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨27, by decide⟩)) ∧
    0 ≤ localCap ⟨27, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid28 :
    envelope (parameters ⟨28, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨28, by decide⟩)) ≤ localCap ⟨28, by decide⟩ ∧
    localCap ⟨28, by decide⟩ - 1/10^9 < envelope (parameters ⟨28, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨28, by decide⟩)) ∧
    0 ≤ localCap ⟨28, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid29 :
    envelope (parameters ⟨29, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨29, by decide⟩)) ≤ localCap ⟨29, by decide⟩ ∧
    localCap ⟨29, by decide⟩ - 1/10^9 < envelope (parameters ⟨29, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨29, by decide⟩)) ∧
    0 ≤ localCap ⟨29, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid30 :
    envelope (parameters ⟨30, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨30, by decide⟩)) ≤ localCap ⟨30, by decide⟩ ∧
    localCap ⟨30, by decide⟩ - 1/10^9 < envelope (parameters ⟨30, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨30, by decide⟩)) ∧
    0 ≤ localCap ⟨30, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid31 :
    envelope (parameters ⟨31, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨31, by decide⟩)) ≤ localCap ⟨31, by decide⟩ ∧
    localCap ⟨31, by decide⟩ - 1/10^9 < envelope (parameters ⟨31, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨31, by decide⟩)) ∧
    0 ≤ localCap ⟨31, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid32 :
    envelope (parameters ⟨32, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨32, by decide⟩)) ≤ localCap ⟨32, by decide⟩ ∧
    localCap ⟨32, by decide⟩ - 1/10^9 < envelope (parameters ⟨32, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨32, by decide⟩)) ∧
    0 ≤ localCap ⟨32, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid33 :
    envelope (parameters ⟨33, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨33, by decide⟩)) ≤ localCap ⟨33, by decide⟩ ∧
    localCap ⟨33, by decide⟩ - 1/10^9 < envelope (parameters ⟨33, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨33, by decide⟩)) ∧
    0 ≤ localCap ⟨33, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid34 :
    envelope (parameters ⟨34, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨34, by decide⟩)) ≤ localCap ⟨34, by decide⟩ ∧
    localCap ⟨34, by decide⟩ - 1/10^9 < envelope (parameters ⟨34, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨34, by decide⟩)) ∧
    0 ≤ localCap ⟨34, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid35 :
    envelope (parameters ⟨35, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨35, by decide⟩)) ≤ localCap ⟨35, by decide⟩ ∧
    localCap ⟨35, by decide⟩ - 1/10^9 < envelope (parameters ⟨35, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨35, by decide⟩)) ∧
    0 ≤ localCap ⟨35, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid36 :
    envelope (parameters ⟨36, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨36, by decide⟩)) ≤ localCap ⟨36, by decide⟩ ∧
    localCap ⟨36, by decide⟩ - 1/10^9 < envelope (parameters ⟨36, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨36, by decide⟩)) ∧
    0 ≤ localCap ⟨36, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid37 :
    envelope (parameters ⟨37, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨37, by decide⟩)) ≤ localCap ⟨37, by decide⟩ ∧
    localCap ⟨37, by decide⟩ - 1/10^9 < envelope (parameters ⟨37, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨37, by decide⟩)) ∧
    0 ≤ localCap ⟨37, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid38 :
    envelope (parameters ⟨38, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨38, by decide⟩)) ≤ localCap ⟨38, by decide⟩ ∧
    localCap ⟨38, by decide⟩ - 1/10^9 < envelope (parameters ⟨38, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨38, by decide⟩)) ∧
    0 ≤ localCap ⟨38, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid39 :
    envelope (parameters ⟨39, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨39, by decide⟩)) ≤ localCap ⟨39, by decide⟩ ∧
    localCap ⟨39, by decide⟩ - 1/10^9 < envelope (parameters ⟨39, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨39, by decide⟩)) ∧
    0 ≤ localCap ⟨39, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid40 :
    envelope (parameters ⟨40, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨40, by decide⟩)) ≤ localCap ⟨40, by decide⟩ ∧
    localCap ⟨40, by decide⟩ - 1/10^9 < envelope (parameters ⟨40, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨40, by decide⟩)) ∧
    0 ≤ localCap ⟨40, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid41 :
    envelope (parameters ⟨41, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨41, by decide⟩)) ≤ localCap ⟨41, by decide⟩ ∧
    localCap ⟨41, by decide⟩ - 1/10^9 < envelope (parameters ⟨41, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨41, by decide⟩)) ∧
    0 ≤ localCap ⟨41, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid42 :
    envelope (parameters ⟨42, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨42, by decide⟩)) ≤ localCap ⟨42, by decide⟩ ∧
    localCap ⟨42, by decide⟩ - 1/10^9 < envelope (parameters ⟨42, by decide⟩)
      (BstLean.Part254.cellUpper (sourceIndex ⟨42, by decide⟩)) ∧
    0 ≤ localCap ⟨42, by decide⟩ := by
  norm_num [envelope, parameters, localCap, sourceIndex, BstLean.Part254.cellUpper,
    BstLean.Part254.worldUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, min_def]

theorem grid (j : Fin 43) :
    envelope (parameters j) (BstLean.Part254.cellUpper (sourceIndex j)) ≤ localCap j ∧
    localCap j - 1/10^9 < envelope (parameters j) (BstLean.Part254.cellUpper (sourceIndex j)) ∧
    0 ≤ localCap j := by
  match j with
  | ⟨0, _⟩ => exact grid0
  | ⟨1, _⟩ => exact grid1
  | ⟨2, _⟩ => exact grid2
  | ⟨3, _⟩ => exact grid3
  | ⟨4, _⟩ => exact grid4
  | ⟨5, _⟩ => exact grid5
  | ⟨6, _⟩ => exact grid6
  | ⟨7, _⟩ => exact grid7
  | ⟨8, _⟩ => exact grid8
  | ⟨9, _⟩ => exact grid9
  | ⟨10, _⟩ => exact grid10
  | ⟨11, _⟩ => exact grid11
  | ⟨12, _⟩ => exact grid12
  | ⟨13, _⟩ => exact grid13
  | ⟨14, _⟩ => exact grid14
  | ⟨15, _⟩ => exact grid15
  | ⟨16, _⟩ => exact grid16
  | ⟨17, _⟩ => exact grid17
  | ⟨18, _⟩ => exact grid18
  | ⟨19, _⟩ => exact grid19
  | ⟨20, _⟩ => exact grid20
  | ⟨21, _⟩ => exact grid21
  | ⟨22, _⟩ => exact grid22
  | ⟨23, _⟩ => exact grid23
  | ⟨24, _⟩ => exact grid24
  | ⟨25, _⟩ => exact grid25
  | ⟨26, _⟩ => exact grid26
  | ⟨27, _⟩ => exact grid27
  | ⟨28, _⟩ => exact grid28
  | ⟨29, _⟩ => exact grid29
  | ⟨30, _⟩ => exact grid30
  | ⟨31, _⟩ => exact grid31
  | ⟨32, _⟩ => exact grid32
  | ⟨33, _⟩ => exact grid33
  | ⟨34, _⟩ => exact grid34
  | ⟨35, _⟩ => exact grid35
  | ⟨36, _⟩ => exact grid36
  | ⟨37, _⟩ => exact grid37
  | ⟨38, _⟩ => exact grid38
  | ⟨39, _⟩ => exact grid39
  | ⟨40, _⟩ => exact grid40
  | ⟨41, _⟩ => exact grid41
  | ⟨42, _⟩ => exact grid42
  | ⟨j + 43, h⟩ => exact False.elim (by omega)

end BstLean.Part255
