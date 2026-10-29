import BstLean.Part271R4SourceA13225Formulas
import BstLean.Part253EnergyUpper

/-! Shared source-energy bounds. Each q is bounded by the smallest grid top. -/
namespace BstLean.Part271.R4.SharedEnergy
open Real Set BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part211 BstLean.Part206
open BstLean.Part182 BstLean.Part271.R4.A13225

theorem energy10 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (132091908459/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (140183189903/200000000000) := by
  have hk1 : kappa q ≤ (628144862787/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (132091908459/250000000000)) (s := (849015690971/1000000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((78751722829/125000000000) : ℝ) ≤ (699184956381/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (78751722829/125000000000)) (s := (776583951479/1000000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (78751722829/125000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (140183189903/200000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (792794383571/1000000000000)) (R := (79331825533/100000000000)) (T := (41830542513/50000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy11 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (26360219861/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (70034598997/100000000000) := by
  have hk1 : kappa q ≤ (156838995497/250000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (26360219861/50000000000)) (s := (424869251521/500000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((629223552631/1000000000000) : ℝ) ≤ (139723199841/200000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (629223552631/1000000000000)) (s := (388612184837/500000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (629223552631/1000000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (70034598997/100000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (792296695577/1000000000000)) (R := (99102570917/125000000000)) (T := (167254077537/200000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy12 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (526041160603/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (17494417017/25000000000) := by
  have hk1 : kappa q ≤ (626567626707/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (526041160603/1000000000000)) (s := (850459109747/1000000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((628433848721/1000000000000) : ℝ) ≤ (87255961413/125000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (628433848721/1000000000000)) (s := (777863032791/1000000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (628433848721/1000000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (17494417017/25000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (791799026611/1000000000000)) (R := (79232289837/100000000000)) (T := (835930175207/1000000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy13 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (524877923987/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (699208020431/1000000000000) := by
  have hk1 : kappa q ≤ (156444949083/250000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (524877923987/1000000000000)) (s := (425588758343/500000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((156911167571/250000000000) : ℝ) ≤ (69748003147/100000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (156911167571/250000000000)) (s := (48656246703/62500000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (156911167571/250000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (699208020431/1000000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (2472816801/3125000000)) (R := (791825248079/1000000000000)) (T := (417795106203/500000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy14 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (523714687371/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (21832500251/31250000000) := by
  have hk1 : kappa q ≤ (624992490251/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (523714687371/1000000000000)) (s := (53243358089/62500000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((626856016713/1000000000000) : ℝ) ≤ (174228254627/250000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (626856016713/1000000000000)) (s := (779135119419/1000000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (626856016713/1000000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (21832500251/31250000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (158160748871/200000000000)) (R := (395663808057/500000000000)) (T := (835250498873/1000000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy15 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (261275725377/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (349036321137/500000000000) := by
  have hk1 : kappa q ≤ (624205707857/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (261275725377/500000000000)) (s := (852607753493/1000000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((313033943697/500000000000) : ℝ) ≤ (348173325607/500000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (313033943697/500000000000)) (s := (389884277823/500000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (313033943697/500000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (349036321137/500000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (197576532591/250000000000)) (R := (790830002123/1000000000000)) (T := (834911034189/1000000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy16 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (260694107069/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (43594120123/62500000000) := by
  have hk1 : kappa q ≤ (311709724273/500000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (260694107069/500000000000)) (s := (53332474649/62500000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((4885002201/7812500000) : ℝ) ≤ (695780928401/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (4885002201/7812500000)) (s := (390200131113/500000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (4885002201/7812500000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (43594120123/62500000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (789808534001/1000000000000)) (R := (77180899/97656250)) (T := (417285908973/500000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy17 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (520224977521/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (348469922959/500000000000) := by
  have hk1 : kappa q ≤ (124526742343/200000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (520224977521/1000000000000)) (s := (854029257557/1000000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((124898639821/200000000000) : ℝ) ≤ (347607924437/500000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (124898639821/200000000000)) (s := (781030245427/1000000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (124898639821/200000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (348469922959/500000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (157862190983/200000000000)) (R := (394917413337/500000000000)) (T := (83423284973/100000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy18 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (103812348181/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (348187206471/500000000000) := by
  have hk1 : kappa q ≤ (310924248383/500000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (103812348181/200000000000)) (s := (427368374219/500000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((623706638931/1000000000000) : ℝ) ≤ (173662852863/250000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (623706638931/1000000000000)) (s := (78165851147/100000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (623706638931/1000000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (348187206471/500000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (394406696381/500000000000)) (R := (789337264521/1000000000000)) (T := (166778825827/200000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy19 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (517898504289/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (173952405463/250000000000) := by
  have hk1 : kappa q ≤ (621063803103/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (517898504289/1000000000000)) (s := (427721036207/500000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((311460300303/500000000000) : ℝ) ≤ (694087614949/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (311460300303/500000000000)) (s := (391142533273/500000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (311460300303/500000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (173952405463/250000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (394157923597/500000000000)) (R := (788839718953/1000000000000)) (T := (833555655751/1000000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy20 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (64591908459/125000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (695245471469/1000000000000) := by
  have hk1 : kappa q ≤ (62027963013/100000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (64591908459/125000000000)) (s := (856145234843/1000000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((38883442721/62500000000) : ℝ) ≤ (173381114547/250000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (38883442721/62500000000)) (s := (782909916807/1000000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (38883442721/62500000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (695245471469/1000000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (393909158933/500000000000)) (R := (6306737517/8000000000)) (T := (208304357293/250000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy21 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (32223251941/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (173670490153/250000000000) := by
  have hk1 : kappa q ≤ (619495977259/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (32223251941/62500000000)) (s := (171369248209/200000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((621350087127/1000000000000) : ℝ) ≤ (692961939991/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (621350087127/1000000000000)) (s := (783533068369/1000000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (621350087127/1000000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (173670490153/250000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (787320804433/1000000000000)) (R := (24620146131/31250000000)) (T := (83287944899/100000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy22 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (514408794439/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (694119088113/1000000000000) := by
  have hk1 : kappa q ≤ (618712843901/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (514408794439/1000000000000)) (s := (85754509631/100000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((310282805397/500000000000) : ℝ) ≤ (69240005919/100000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (310282805397/500000000000)) (s := (78415452731/100000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (310282805397/500000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (694119088113/1000000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (786823306553/1000000000000)) (R := (98418397289/125000000000)) (T := (832541714803/1000000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy23 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (513245557823/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (346778426399/500000000000) := by
  have hk1 : kappa q ≤ (61793022947/100000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (513245557823/1000000000000)) (s := (858241805889/1000000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((619781653947/1000000000000) : ℝ) ≤ (138367762923/200000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (619781653947/1000000000000)) (s := (196193574919/250000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (619781653947/1000000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (346778426399/500000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (393162911941/500000000000)) (R := (786849695641/1000000000000)) (T := (832204226207/1000000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy24 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (256041160603/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (346497626753/500000000000) := by
  have hk1 : kappa q ≤ (617148133383/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (256041160603/500000000000)) (s := (429468187503/500000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((123799643201/200000000000) : ℝ) ≤ (345639102551/500000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (123799643201/200000000000)) (s := (785392391473/1000000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (123799643201/200000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (346497626753/500000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (785828356079/1000000000000)) (R := (393176113919/500000000000)) (T := (415933491401/500000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy25 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (51091908459/100000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (346217144537/500000000000) := by
  have hk1 : kappa q ≤ (77045819383/125000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (51091908459/100000000000)) (s := (859628808849/1000000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((154553824097/250000000000) : ℝ) ≤ (345359114747/500000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (154553824097/250000000000)) (s := (393004404337/500000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (154553824097/250000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (346217144537/500000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (196332725701/250000000000)) (R := (785854774563/1000000000000)) (T := (207882496047/250000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy26 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (254877923987/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (34593697917/50000000000) := by
  have hk1 : kappa q ≤ (153896373483/250000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (254877923987/500000000000)) (s := (215079778143/250000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((123486578903/200000000000) : ℝ) ≤ (69015888663/100000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (123486578903/200000000000)) (s := (786623557219/1000000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (123486578903/200000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (34593697917/50000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (156966692743/200000000000)) (R := (392678667737/500000000000)) (T := (207798307491/250000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy27 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (508592611357/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (86414282519/125000000000) := by
  have hk1 : kappa q ≤ (122960989883/200000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (508592611357/1000000000000)) (s := (861007291301/1000000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((616651009813/1000000000000) : ℝ) ≤ (689600175359/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (616651009813/1000000000000)) (s := (78723664301/100000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (616651009813/1000000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (86414282519/125000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (392168019237/500000000000)) (R := (784859910233/1000000000000)) (T := (415428359867/500000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy28 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (507429374741/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (8634439917/12500000000) := by
  have hk1 : kappa q ≤ (614024920941/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (507429374741/1000000000000)) (s := (430846675063/500000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((615869641711/1000000000000) : ℝ) ≤ (689042094533/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (615869641711/1000000000000)) (s := (157569614383/200000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (615869641711/1000000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (8634439917/12500000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (97979828343/125000000000)) (R := (784362498503/1000000000000)) (T := (830520453103/1000000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy29 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (126566534531/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (43137297301/62500000000) := by
  have hk1 : kappa q ≤ (306622703971/500000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (126566534531/250000000000)) (s := (431188647053/500000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((153772197409/250000000000) : ℝ) ≤ (172121160751/250000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (153772197409/250000000000)) (s := (788457849771/1000000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (153772197409/250000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (43137297301/62500000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (391670614093/500000000000)) (R := (156773019989/200000000000)) (T := (33207377187/40000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy30 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (126275725377/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (344819474689/500000000000) := by
  have hk1 : kappa q ≤ (612466409853/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (126275725377/250000000000)) (s := (863059128269/1000000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((24572338121/40000000000) : ℝ) ≤ (343963909817/500000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (24572338121/40000000000)) (s := (98633247797/125000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (24572338121/40000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (344819474689/500000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (391421921233/500000000000)) (R := (31334708569/40000000000)) (T := (414924324529/500000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy31 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (125984916223/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (689081769907/1000000000000) := by
  have hk1 : kappa q ≤ (611687926111/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (125984916223/250000000000)) (s := (215934714403/250000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((306764315657/500000000000) : ℝ) ≤ (171842905821/250000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (306764315657/500000000000)) (s := (394836237749/500000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (306764315657/500000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (689081769907/1000000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (6112081791/7812500000)) (R := (782870341007/1000000000000)) (T := (829513110861/1000000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy32 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (20111057131/40000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (137705043453/200000000000) := by
  have hk1 : kappa q ≤ (122181991231/200000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (20111057131/40000000000)) (s := (864416487101/1000000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((612749323941/1000000000000) : ℝ) ≤ (686816052819/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (612749323941/1000000000000)) (s := (790277334871/1000000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (612749323941/1000000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (137705043453/200000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (390924554099/500000000000)) (R := (782372979957/1000000000000)) (T := (207294453673/250000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy33 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (501613191659/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (687969290323/1000000000000) := by
  have hk1 : kappa q ≤ (61013249943/100000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (501613191659/1000000000000)) (s := (865092021669/1000000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((611970530349/1000000000000) : ℝ) ≤ (686261107111/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (611970530349/1000000000000)) (s := (158176113239/200000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (611970530349/1000000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (687969290323/1000000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (390675879491/500000000000)) (R := (781875630741/1000000000000)) (T := (207210690041/250000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy34 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (250224977521/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (13748279759/20000000000) := by
  have hk1 : kappa q ≤ (304677777689/500000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (250224977521/500000000000)) (s := (43288273311/50000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((611192249979/1000000000000) : ℝ) ≤ (685706785031/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (611192249979/1000000000000)) (s := (791482175141/1000000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (611192249979/1000000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (13748279759/20000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (780854421267/1000000000000)) (R := (390689146513/500000000000)) (T := (103563493361/125000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy35 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (249643359213/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (27474372361/40000000000) := by
  have hk1 : kappa q ≤ (608579123451/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (249643359213/500000000000)) (s := (216609206407/250000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((152603620571/250000000000) : ℝ) ≤ (34257654273/50000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (152603620571/250000000000)) (s := (39604108367/50000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (152603620571/250000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (27474372361/40000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (195089273681/250000000000)) (R := (780880966483/1000000000000)) (T := (10352167181/12500000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy36 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (498123481809/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (686305252429/1000000000000) := by
  have hk1 : kappa q ≤ (607803203099/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (498123481809/1000000000000)) (s := (867106104737/1000000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((60963722671/100000000000) : ℝ) ≤ (684600007277/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (60963722671/100000000000)) (s := (792680548399/1000000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (60963722671/100000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (686305252429/1000000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (38992988951/50000000000)) (R := (780383650779/1000000000000)) (T := (206959760639/250000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy37 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (496960245193/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (8571897713/12500000000) := by
  have hk1 : kappa q ≤ (37939237111/62500000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (496960245193/1000000000000)) (s := (433886654179/500000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((608860482713/1000000000000) : ℝ) ≤ (85505943671/125000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (608860482713/1000000000000)) (s := (396638661943/500000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (608860482713/1000000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (8571897713/12500000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (779362473827/1000000000000)) (R := (389943172793/500000000000)) (T := (827504950731/1000000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy38 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (495797008577/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (685199001753/1000000000000) := by
  have hk1 : kappa q ≤ (30312644747/50000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (495797008577/1000000000000)) (s := (868438441277/1000000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((2432336999/4000000000) : ℝ) ≤ (21359240957/31250000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (2432336999/4000000000)) (s := (793872499339/1000000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (2432336999/4000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (685199001753/1000000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (389432589409/500000000000)) (R := (779389050577/1000000000000)) (T := (827171098627/1000000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy39 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (12365844299/25000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (684646805453/1000000000000) := by
  have hk1 : kappa q ≤ (9460601657/15625000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (12365844299/25000000000)) (s := (869101508247/1000000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((24292341091/40000000000) : ℝ) ≤ (341472244967/500000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (24292341091/40000000000)) (s := (79446608027/100000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (24292341091/40000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (684646805453/1000000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (778367893661/1000000000000)) (R := (38944588271/50000000000)) (T := (826837485861/1000000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy40 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (30841908459/62500000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (684095227037/1000000000000) := by
  have hk1 : kappa q ≤ (302352313283/500000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (30841908459/62500000000)) (s := (869762513993/1000000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((303266657377/500000000000) : ℝ) ≤ (341196943099/500000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (303266657377/500000000000)) (s := (99382259019/125000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (303266657377/500000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (684095227037/1000000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (388935309017/500000000000)) (R := (778394489793/1000000000000)) (T := (103313014007/125000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy41 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (492307298727/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (341772132703/500000000000) := by
  have hk1 : kappa q ≤ (603931255957/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (492307298727/1000000000000)) (s := (870421463213/1000000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((12115172233/20000000000) : ℝ) ≤ (170460974579/250000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (12115172233/20000000000)) (s := (795648480431/1000000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (12115172233/20000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (341772132703/500000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (777373351609/1000000000000)) (R := (97237152921/125000000000)) (T := (206542744209/250000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy42 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (491144062111/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (341496959731/500000000000) := by
  have hk1 : kappa q ≤ (60315839369/100000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (491144062111/1000000000000)) (s := (87107836057/100000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((60498441743/100000000000) : ℝ) ≤ (681294525191/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (60498441743/100000000000)) (s := (398118655261/500000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (60498441743/100000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (341496959731/500000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (388438047031/500000000000)) (R := (777399965821/1000000000000)) (T := (33033523193/40000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy43 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (97996165099/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (68244418811/100000000000) := by
  have hk1 : kappa q ≤ (150596509809/250000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (97996165099/200000000000)) (s := (435866605353/500000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((151052682891/250000000000) : ℝ) ≤ (680745765733/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (151052682891/250000000000)) (s := (796824567809/1000000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (151052682891/250000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (68244418811/100000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (776378845069/1000000000000)) (R := (194225679207/250000000000)) (T := (825505420649/1000000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy44 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (244408794439/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (681895070261/1000000000000) := by
  have hk1 : kappa q ≤ (150403548017/250000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (244408794439/500000000000)) (s := (872386018231/1000000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((150859388381/250000000000) : ℝ) ≤ (680197618853/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (150859388381/250000000000)) (s := (159482051529/200000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (150859388381/250000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (681895070261/1000000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (775881604307/1000000000000)) (R := (388202738033/500000000000)) (T := (103146624867/125000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy45 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (243827176131/500000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (340673282417/500000000000) := by
  have hk1 : kappa q ≤ (37552678229/62500000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (243827176131/500000000000)) (s := (34921471509/40000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((150666220697/250000000000) : ℝ) ≤ (679650083469/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (150666220697/250000000000)) (s := (797994385353/1000000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (150666220697/250000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (340673282417/500000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (3028845201/3906250000)) (R := (155181648643/200000000000)) (T := (824840814317/1000000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy46 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (97298223129/200000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (680798670739/1000000000000) := by
  have hk1 : kappa q ≤ (600072017501/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (97298223129/200000000000)) (s := (27302672617/31250000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((37618294927/62500000000) : ℝ) ≤ (339551579249/500000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (37618294927/62500000000)) (s := (199644239057/250000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (37618294927/62500000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (680798670739/1000000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (774887146193/1000000000000)) (R := (24231594311/31250000000)) (T := (824508866419/1000000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy47 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (485327879029/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (170062846727/250000000000) := by
  have hk1 : kappa q ≤ (74912711133/125000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (485327879029/1000000000000)) (s := (874332230813/1000000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((300560530571/500000000000) : ℝ) ≤ (169639210717/250000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (300560530571/500000000000)) (s := (799157975529/1000000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (300560530571/500000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (170062846727/250000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (774389928201/1000000000000)) (R := (19372844999/25000000000)) (T := (2575553609/3125000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy48 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (121041160603/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (679704712259/1000000000000) := by
  have hk1 : kappa q ≤ (119706373167/200000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (121041160603/250000000000)) (s := (109372114179/125000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((120069981839/200000000000) : ℝ) ≤ (339005567751/500000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (120069981839/200000000000)) (s := (399868724249/500000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (120069981839/200000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (679704712259/1000000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (386946358579/500000000000)) (R := (774416588917/1000000000000)) (T := (823845679329/1000000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy49 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (120750351449/250000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (169789661431/250000000000) := by
  have hk1 : kappa q ≤ (119552509461/200000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (120750351449/250000000000)) (s := (109452447009/125000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((299789631241/500000000000) : ℝ) ≤ (677466035333/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (299789631241/500000000000)) (s := (50019711271/62500000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (299789631241/500000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (169789661431/250000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (193348878187/250000000000)) (R := (773919384507/1000000000000)) (T := (823514439403/1000000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy50 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (24091908459/50000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (678613186239/1000000000000) := by
  have hk1 : kappa q ≤ (596993732961/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (24091908459/50000000000)) (s := (876260223177/1000000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((149702280123/250000000000) : ℝ) ≤ (338460770649/500000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (149702280123/250000000000)) (s := (40044588811/50000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (149702280123/250000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (678613186239/1000000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (386449157327/500000000000)) (R := (773422186413/1000000000000)) (T := (41159171737/50000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy51 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (480674932563/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (33903416637/50000000000) := by
  have hk1 : kappa q ≤ (298112711149/500000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (480674932563/1000000000000)) (s := (438449429583/500000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((598039482717/1000000000000) : ℝ) ≤ (135275530467/200000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (598039482717/1000000000000)) (s := (801466641297/1000000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (598039482717/1000000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (33903416637/50000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (603438377/781250000)) (R := (772924994319/1000000000000)) (T := (411426332489/500000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem energy52 {n : ℕ} (ha : 13225 ≤ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (479511695947/1000000000000)) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) q ≤ (677524084169/1000000000000) := by
  have hk1 : kappa q ≤ (595457614813/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (479511695947/1000000000000)) (s := (219383872107/250000000000))
    · exact hq0
    · exact hq
    all_goals norm_num
  have hk2 : kappa ((298635174327/500000000000) : ℝ) ≤ (675834367387/1000000000000) := by
    apply BstLean.Part253.kappa_upper_rational (Q := (298635174327/500000000000)) (s := (401019990343/500000000000))
    all_goals norm_num
  have h : energyRatio n (gMinus n) q ≤ (298635174327/500000000000) ∧
      energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11/1000)) q ≤ (677524084169/1000000000000) := by
    apply BstLean.Part277.energy_upper_from_kappasP (n0 := 13225) (by norm_num) ha
      (U := (96487992019/125000000000)) (R := (772427807911/1000000000000)) (T := (411261064879/500000000000))
      (t := 3.464102) (t2 := (1732958180071/500000000000)) (g0 := (249738129383/250000000000))
      (s0 := 0.9999999933) (G := (500524008979/500000000000)) (r := 115)
      (ht := sqrt_le_iff.mpr (by norm_num))
      (hs0 := le_sqrt_of_sq_le (by norm_num))
      (ht2 := sqrt_le_iff.mpr (by norm_num))
      (hF := source_finite ha) (hK1 := hk1) (hK2 := hk2)
    all_goals norm_num
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

end BstLean.Part271.R4.SharedEnergy
